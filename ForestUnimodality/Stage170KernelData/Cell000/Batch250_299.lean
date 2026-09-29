import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell000.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch250_299
import ForestUnimodality.BinomialMassData.Q9_35.Batch250_299

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel250
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/50000000000000000000)
  centralHi := (434116806372142490547/100000000000000000000)
  directionLo := (6796736896083765141/1562500000000000000)
  directionHi := (17399646453974438761/4000000000000000000)

def endpointA : IntegerEndpointWitness 250 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree250.table
  base := (-494923920513579138860213461426978381411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-59306314928752868892436469280000000000000)
      constant := (1830069935585615338769553247308584172948712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 250 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree250.table
  base := (-494923920513812143454060911309773418187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3737378249327563718359957028400000000000000)
      constant := (118672042517756036879189232193458211025088370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 250 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel251
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6796736896083765141/1562500000000000000)
  centralHi := (17399646453974438761/4000000000000000000)
  directionLo := (435863762349410416613/100000000000000000000)
  directionHi := (217931881174705208307/50000000000000000000)

def endpointA : IntegerEndpointWitness 251 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree251.table
  base := (-218841548829297660100127202086432320367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-59546009694333327175175265360000000000000)
      constant := (1845384402746340983827284386596617082874128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 251 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree251.table
  base := (-35014647812703973335355115582570130681/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3752479019559132590172501181440000000000000)
      constant := (119663072169811853946756845155464757949578875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 251 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel252
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435863762349410416613/100000000000000000000)
  centralHi := (217931881174705208307/50000000000000000000)
  directionLo := (436734619885693118087/100000000000000000000)
  directionHi := (54591827485711639761/12500000000000000000)

def endpointA : IntegerEndpointWitness 252 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree252.table
  base := (-189999600383115000029955307716042485179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-59785704459913785457914061440000000000000)
      constant := (1860762338190760795467543302756543320237136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 252 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree252.table
  base := (-151999680306563684243460403041337379739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-538225684255814494569292190640000000000000)
      constant := (17236885997621198521196028277083765958545675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 252 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel253
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436734619885693118087/100000000000000000000)
  centralHi := (54591827485711639761/12500000000000000000)
  directionLo := (218801872183499830781/50000000000000000000)
  directionHi := (437603744366999661563/100000000000000000000)

def endpointA : IntegerEndpointWitness 253 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree253.table
  base := (-643744469603811374080267152528330661731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-60025399225494243740652857520000000000000)
      constant := (1876203741879151393621522383939886677353076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 253 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree253.table
  base := (-321872234802062851262845727520122333607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3782680560022270333797589487520000000000000)
      constant := (121657431955932587166766552718227140056532570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 253 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel254
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/50000000000000000000)
  centralHi := (437603744366999661563/100000000000000000000)
  directionLo := (438471146098960451669/100000000000000000000)
  directionHi := (43847114609896045167/10000000000000000000)

def endpointA : IntegerEndpointWitness 254 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree254.table
  base := (-52660440936625221587766384226739111343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-60265093991074702023391653600000000000000)
      constant := (1891708613772172748474838361070930435546280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 254 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree254.table
  base := (-526604409366527871968736472521671749689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3797781330253839205610133640560000000000000)
      constant := (122660762085154869861748285376840190421326195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 254 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel255
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438471146098960451669/100000000000000000000)
  centralHi := (43847114609896045167/10000000000000000000)
  directionLo := (878673670570942861/200000000000000000)
  directionHi := (439336835285471430501/100000000000000000000)

def endpointA : IntegerEndpointWitness 255 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree255.table
  base := (-25536139410015062094466484167693521571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-60504788756655160306130449680000000000000)
      constant := (1907276953830863026155493424363267614619456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 255 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree255.table
  base := (-204289115280241365872582636927351013569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3812882100485408077422677793600000000000000)
      constant := (123668192368628825571778707504905598003351190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 255 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel256
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (878673670570942861/200000000000000000)
  centralHi := (439336835285471430501/100000000000000000000)
  directionLo := (440200822030094564299/100000000000000000000)
  directionHi := (4402008220300945643/1000000000000000000)

def endpointA : IntegerEndpointWitness 256 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree256.table
  base := (-72416485708238399640792339552474222711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-60744483522235618588869245760000000000000)
      constant := (1922908762016633523097161563847160412436624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 256 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree256.table
  base := (-9052060713536424667245921933749708939/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3827982870716976949235221946640000000000000)
      constant := (124679722803990896346521080649927402281918240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 256 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel257
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440200822030094564299/100000000000000000000)
  centralHi := (4402008220300945643/1000000000000000000)
  directionLo := (55132889542179204951/12500000000000000000)
  directionHi := (441063116337433639609/100000000000000000000)

def endpointA : IntegerEndpointWitness 257 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree257.table
  base := (-169867555739528050650542114909118871279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-60984178287816076871608041840000000000000)
      constant := (1938604038291263687221371733770363524514884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 257 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree257.table
  base := (-84933777869856976008805154246591672689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3843083640948545821047766099680000000000000)
      constant := (125695353388900073496704358329691170080382390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 257 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel258
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/12500000000000000000)
  centralHi := (441063116337433639609/100000000000000000000)
  directionLo := (441923728114485898847/100000000000000000000)
  directionHi := (13810116503577684339/3125000000000000000)

def endpointA : IntegerEndpointWitness 258 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree258.table
  base := (-49183078744287949751605855060116946061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-61223873053396535154346837920000000000000)
      constant := (1954362782616896224128211838779759532215756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 258 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree258.table
  base := (-2459153937222548511706875965334865617/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3858184411180114692860310252720000000000000)
      constant := (126715084121037597850458061836921859158476700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 258 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel259
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441923728114485898847/100000000000000000000)
  centralHi := (13810116503577684339/3125000000000000000)
  directionLo := (1729619793640507937/390625000000000000)
  directionHi := (442782667171970031873/100000000000000000000)

def endpointA : IntegerEndpointWitness 259 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree259.table
  base := (36193739389027441042119946712737051773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-61463567818976993437085634000000000000000)
      constant := (1970184994956032286529484280763701896414184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 259 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree259.table
  base := (36193739388955964124104010129915562683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-553326454487383366381836343680000000000000)
      constant := (18248416428300952158283336809213094089387810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 259 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel260
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1729619793640507937/390625000000000000)
  centralHi := (442782667171970031873/100000000000000000000)
  directionLo := (443639943225631027071/100000000000000000000)
  directionHi := (3465937056450242399/781250000000000000)

def endpointA : IntegerEndpointWitness 260 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree260.table
  base := (194844107541218138944821274252436861137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-61703262584557451719824430080000000000000)
      constant := (1986070675271526745201540364297009747444548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 260 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree260.table
  base := (194844107541092783399110289747599332103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3888385951643252436485398558800000000000000)
      constant := (128766846017832136189072818387388161836365235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 260 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel261
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443639943225631027071/100000000000000000000)
  centralHi := (3465937056450242399/781250000000000000)
  directionLo := (444495565897522372927/100000000000000000000)
  directionHi := (6945243217148787077/1562500000000000000)

def endpointA : IntegerEndpointWitness 261 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree261.table
  base := (318186798346186728984729303139855786769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-61942957350137910002563226160000000000000)
      constant := (2002019823526583539776998453442559423147076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 261 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree261.table
  base := (4971668724157450105907608168368239087/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3903486721874821308297942711840000000000000)
      constant := (129798877177960252470558525825848013988884160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 261 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel262
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444495565897522372927/100000000000000000000)
  centralHi := (6945243217148787077/1562500000000000000)
  directionLo := (44534954471726608873/10000000000000000000)
  directionHi := (445349544717266088731/100000000000000000000)

def endpointA : IntegerEndpointWitness 262 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree262.table
  base := (221207771040035011048105213345076847867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-62182652115718368285302022240000000000000)
      constant := (2018032439684751107735427533986760614782936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 262 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree262.table
  base := (221207771039986817208750161905158532127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3918587492106390180110486864880000000000000)
      constant := (130835008476258355813268408768965527680742230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 262 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel263
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44534954471726608873/10000000000000000000)
  centralHi := (445349544717266088731/100000000000000000000)
  directionLo := (89240377824658210237/20000000000000000000)
  directionHi := (223100944561645525593/50000000000000000000)

def endpointA : IntegerEndpointWitness 263 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree263.table
  base := (567530329714978247233603700942597578669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-62422346881298826568040818320000000000000)
      constant := (2034108523709917889992644962153770390314676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 263 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree263.table
  base := (567530329714893728720135514869510002943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3933688262337959051923031017920000000000000)
      constant := (131875239910514613280491149547135029950721035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 263 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel264
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89240377824658210237/20000000000000000000)
  centralHi := (223100944561645525593/50000000000000000000)
  directionLo := (447052608464050072107/100000000000000000000)
  directionHi := (111763152116012518027/25000000000000000000)

def endpointA : IntegerEndpointWitness 264 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree264.table
  base := (173382788076729412239438284496573598897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-62662041646879284850779614400000000000000)
      constant := (2050248075566307911526894113991945177582352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 264 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree264.table
  base := (693531152306843539016034080754527596627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3948789032569527923735575170960000000000000)
      constant := (132919571478537746452312608348632859261173615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 264 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel265
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447052608464050072107/100000000000000000000)
  centralHi := (111763152116012518027/25000000000000000000)
  directionLo := (223950855999608085589/50000000000000000000)
  directionHi := (447901711999216171179/100000000000000000000)

def endpointA : IntegerEndpointWitness 265 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree265.table
  base := (820418000994704022163620765511771641333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-62901736412459743133518410480000000000000)
      constant := (2066451095218476435517754837612047086565332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 265 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree265.table
  base := (820418000994639039810495189584165329639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3963889802801096795548119324000000000000000)
      constant := (133968003178156765242486583469648120505761555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 265 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel266
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/50000000000000000000)
  centralHi := (447901711999216171179/100000000000000000000)
  directionLo := (448749208900858476759/100000000000000000000)
  directionHi := (11218730222521461919/2500000000000000000)

def endpointA : IntegerEndpointWitness 266 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree266.table
  base := (237047716749723563251054775428257218547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-63141431178040201416257206560000000000000)
      constant := (2082717582631305689509839183086852115496752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 266 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree266.table
  base := (474095433499418637398321358160769303451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-568427224718952238194380496720000000000000)
      constant := (19288647858174386589531127179935253851241570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 266 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel267
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448749208900858476759/100000000000000000000)
  centralHi := (11218730222521461919/2500000000000000000)
  directionLo := (7024923566478096519/1562500000000000000)
  directionHi := (449595108254598177217/100000000000000000000)

def endpointA : IntegerEndpointWitness 267 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree267.table
  base := (1076849741620735502965651440264655513969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-63381125943620659698996002640000000000000)
      constant := (2099047537770000662149091563591058622055876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 267 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree267.table
  base := (134606217702585692955031188070628906587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3994091343264234539173207630080000000000000)
      constant := (136077166963598374693424643065010432656910520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 267 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel268
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7024923566478096519/1562500000000000000)
  centralHi := (449595108254598177217/100000000000000000000)
  directionLo := (225219709530372467419/50000000000000000000)
  directionHi := (450439419060744934839/100000000000000000000)

def endpointA : IntegerEndpointWitness 268 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree268.table
  base := (1206394616241131681596385805247320243019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-63620820709201117981734798720000000000000)
      constant := (2115440960600084969073705851220989280972076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 268 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree268.table
  base := (120639461624108787708637156140434491553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4009192113495803410985751783120000000000000)
      constant := (137137899045178092430139380607776064504304850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 268 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel269
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225219709530372467419/50000000000000000000)
  centralHi := (450439419060744934839/100000000000000000000)
  directionLo := (14102567194856692639/3125000000000000000)
  directionHi := (451282150235414164449/100000000000000000000)

def endpointA : IntegerEndpointWitness 269 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree269.table
  base := (66841274115981343091213118687514848453/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-63860515474781576264473594800000000000000)
      constant := (2131897851087396786575393406685001187876240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 269 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree269.table
  base := (1336825482319588454362035045295492842773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4024292883727372282798295936160000000000000)
      constant := (138202731249867447660772724296665395746479385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 269 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel270
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/3125000000000000000)
  centralHi := (451282150235414164449/100000000000000000000)
  directionLo := (452123310611625569043/100000000000000000000)
  directionHi := (113030827652906392261/25000000000000000000)

def endpointA : IntegerEndpointWitness 270 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree270.table
  base := (734071165696702649963308706097916110629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-64100210240362034547212390880000000000000)
      constant := (2148418209198084851679263575048783328885032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 270 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree270.table
  base := (58725693255734864999044536122987005231/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4039393653958941154610840089200000000000000)
      constant := (139271663575593050550954348126153295407039875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 270 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel271
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452123310611625569043/100000000000000000000)
  centralHi := (113030827652906392261/25000000000000000000)
  directionLo := (113240727235095828831/25000000000000000000)
  directionHi := (18118516357615332613/4000000000000000000)

def endpointA : IntegerEndpointWitness 271 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree271.table
  base := (1600345155076307730148651398577054965031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-64339905005942492829951186960000000000000)
      constant := (2165002034898604527322297158224308219860124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 271 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree271.table
  base := (400086288769069551235724523005741298147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4054494424190510026423384242240000000000000)
      constant := (140344696020300292100607753503273626472184060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 271 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel272
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113240727235095828831/25000000000000000000)
  centralHi := (18118516357615332613/4000000000000000000)
  directionLo := (113450238472934555699/25000000000000000000)
  directionHi := (453800953891738222797/100000000000000000000)

def endpointA : IntegerEndpointWitness 272 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree272.table
  base := (866716972528931805856244403889248134141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-64579599771522951112689983040000000000000)
      constant := (2181649328155713931341382654111113985073128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 272 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree272.table
  base := (173343394505783772519934323292998605433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4069595194422078898235928395280000000000000)
      constant := (141421828581953107044812494187619846583310850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 272 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel273
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113450238472934555699/25000000000000000000)
  centralHi := (453800953891738222797/100000000000000000000)
  directionLo := (227318727027916165559/50000000000000000000)
  directionHi := (454637454055832331119/100000000000000000000)

def endpointA : IntegerEndpointWitness 273 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree273.table
  base := (466852173275584753355809091437455314141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-64819294537103409395428779120000000000000)
      constant := (2198360088936470128011740489612999285026256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 273 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree273.table
  base := (1867408693102316317446451168779737941543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-583527994950521110006924649760000000000000)
      constant := (20357580179790534369405045107603290827954005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 273 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel274
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/50000000000000000000)
  centralHi := (454637454055832331119/100000000000000000000)
  directionLo := (18218896717757048069/4000000000000000000)
  directionHi := (227736208971963100863/50000000000000000000)

def endpointA : IntegerEndpointWitness 274 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree274.table
  base := (2002269391047799828438696215236958561991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-65058989302683867678167575200000000000000)
      constant := (2215134317208225380906001873300947834247964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 274 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree274.table
  base := (1001134695523889965001327784246668905341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4099796734885216641861016701360000000000000)
      constant := (143588394048042518881014234448968867763617090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 274 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel275
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18218896717757048069/4000000000000000000)
  centralHi := (227736208971963100863/50000000000000000000)
  directionLo := (11407646349735232531/2500000000000000000)
  directionHi := (456305853989409301241/100000000000000000000)

def endpointA : IntegerEndpointWitness 275 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree275.table
  base := (2138016030805190018847100199467301761453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-65298684068264325960906371280000000000000)
      constant := (2231972012938623465872519732547869207045812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 275 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree275.table
  base := (1069008015402586286666085391332726309953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4114897505116785513673560854400000000000000)
      constant := (144677826948497623212912982790753035891876970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 275 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel276
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11407646349735232531/2500000000000000000)
  centralHi := (456305853989409301241/100000000000000000000)
  directionLo := (28571110659299612873/6250000000000000000)
  directionHi := (457137770548793805969/100000000000000000000)

def endpointA : IntegerEndpointWitness 276 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree276.table
  base := (1137324302178712298316621678974448207743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-65538378833844784243645167360000000000000)
      constant := (2248873176095596042959233247511795585661944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 276 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree276.table
  base := (1137324302178704650922504166945267493793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4129998275348354385486105007440000000000000)
      constant := (145771359957934867769862013601611181071958570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 276 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel277
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28571110659299612873/6250000000000000000)
  centralHi := (457137770548793805969/100000000000000000000)
  directionLo := (91593635180538431753/20000000000000000000)
  directionHi := (228984087951346079383/50000000000000000000)

def endpointA : IntegerEndpointWitness 277 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree277.table
  base := (2412167103758497054368375642667217502937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-65778073599425242526383963440000000000000)
      constant := (2265837806647359086136427418000668870011748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 277 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree277.table
  base := (1206083551879241822659170863695494561249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4145099045579923257298649160480000000000000)
      constant := (146868993074407480966656734390322792335012010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 277 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel278
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91593635180538431753/20000000000000000000)
  centralHi := (228984087951346079383/50000000000000000000)
  directionLo := (229398539128389350873/50000000000000000000)
  directionHi := (458797078256778701747/100000000000000000000)

def endpointA : IntegerEndpointWitness 278 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree278.table
  base := (2550571521132600965487235899576129744103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-66017768365005700809122759520000000000000)
      constant := (2282865904562409369697841199398304518976412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 278 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree278.table
  base := (1275285760566294604907585080263751455663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4160199815811492129111193313520000000000000)
      constant := (147970726295985890236782579960241238213274870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 278 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel279
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229398539128389350873/50000000000000000000)
  centralHi := (458797078256778701747/100000000000000000000)
  directionLo := (229812242871367850381/50000000000000000000)
  directionHi := (459624485742735700763/100000000000000000000)

def endpointA : IntegerEndpointWitness 279 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree279.table
  base := (2689861848673265480457269530142534381111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-66257463130586159091861555600000000000000)
      constant := (2299957469809521010245344373310570137524444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 279 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree279.table
  base := (1344930924336627587208174219565367615547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4175300586043061000923737466560000000000000)
      constant := (149076559620757510229114359738795030131618030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 279 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel280
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229812242871367850381/50000000000000000000)
  centralHi := (459624485742735700763/100000000000000000000)
  directionLo := (23022520320959203507/5000000000000000000)
  directionHi := (460450406419184070141/100000000000000000000)

def endpointA : IntegerEndpointWitness 280 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree280.table
  base := (707509519660626112827444714042319051317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-66497157896166617374600351680000000000000)
      constant := (2317112502357742063187062149024677104821072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 280 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree280.table
  base := (1415019039321247708122703038409838181991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-598628765182089981819468802800000000000000)
      constant := (21455213292403790620506762636688688672739370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 280 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel281
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23022520320959203507/5000000000000000000)
  centralHi := (460450406419184070141/100000000000000000000)
  directionLo := (57659356034074887381/12500000000000000000)
  directionHi := (461274848272599099049/100000000000000000000)

def endpointA : IntegerEndpointWitness 281 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree281.table
  base := (2971100203369978923113484527002982648853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-66736852661747075657339147760000000000000)
      constant := (2334331002176391172703269409138011930595412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 281 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree281.table
  base := (2971100203369971002375121540678214063637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4205502126506198744548825772640000000000000)
      constant := (151300526572313729541514346838754162445591065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 281 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel282
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/12500000000000000000)
  centralHi := (461274848272599099049/100000000000000000000)
  directionLo := (462097819218211473823/100000000000000000000)
  directionHi := (14440556850569108557/3125000000000000000)

def endpointA : IntegerEndpointWitness 282 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree282.table
  base := (3113048215252172736837395718399493606657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-66976547427327533940077943840000000000000)
      constant := (2351612969235054274157842190353597974426628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 282 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree282.table
  base := (622609643050433158614039206592989955577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4220602896737767616361369925680000000000000)
      constant := (152418660195356234368780236679148412695581825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 282 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel283
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462097819218211473823/100000000000000000000)
  centralHi := (14440556850569108557/3125000000000000000)
  directionLo := (462919327100893883819/100000000000000000000)
  directionHi := (23145966355044694191/5000000000000000000)

def endpointA : IntegerEndpointWitness 283 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree283.table
  base := (40698526334394762422765993386240502747/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-67216242192907992222816739920000000000000)
      constant := (2368958403503581347956139560833596960879040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 283 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree283.table
  base := (651176421350314981318170073753309587291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4235703666969336488173914078720000000000000)
      constant := (153540893914107360129318762077699804244431475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 283 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel284
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462919327100893883819/100000000000000000000)
  centralHi := (23145966355044694191/5000000000000000000)
  directionLo := (92747875939206698339/20000000000000000000)
  directionHi := (28983711231002093231/6250000000000000000)

def endpointA : IntegerEndpointWitness 284 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree284.table
  base := (3399601870395911137656968200558785391293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-67455936958488450505555536000000000000000)
      constant := (2386367304952083223872528850242235141565172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 284 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree284.table
  base := (849900467598976450341578926833793295061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4250804437200905359986458231760000000000000)
      constant := (154667227726736395150445084668425117429159780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 284 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel285
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92747875939206698339/20000000000000000000)
  centralHi := (28983711231002093231/6250000000000000000)
  directionLo := (3716463877683124341/800000000000000000)
  directionHi := (232278992355195271313/50000000000000000000)

def endpointA : IntegerEndpointWitness 285 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree285.table
  base := (3544207498777296414748659770240120401521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-67695631724068908788294332080000000000000)
      constant := (2403839673550928434892626850030960481606084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 285 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree285.table
  base := (44302593734716146710142512490456122487/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4265905207432474231799002384800000000000000)
      constant := (155797661631428412080715832644212940000745200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 285 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel286
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3716463877683124341/800000000000000000)
  centralHi := (232278992355195271313/50000000000000000000)
  directionLo := (465375149782943380639/100000000000000000000)
  directionHi := (2908594686143396129/625000000000000000)

def endpointA : IntegerEndpointWitness 286 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree286.table
  base := (3689698984551521480139918756723778157921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-67935326489649367071033128160000000000000)
      constant := (2421375509270740119636607818506895112631684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 286 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree286.table
  base := (3689698984551517379378257214875441880801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4281005977664043103611546537840000000000000)
      constant := (156932195626384078163411782992812483260796245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 286 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel287
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465375149782943380639/100000000000000000000)
  centralHi := (2908594686143396129/625000000000000000)
  directionLo := (116547720621430033543/25000000000000000000)
  directionHi := (466190882485720134173/100000000000000000000)

def endpointA : IntegerEndpointWitness 287 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree287.table
  base := (959019080109314980088478859731985541911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-68175021255229825353771924240000000000000)
      constant := (2438974812082392972450564436785711768670576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 287 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree287.table
  base := (479509540054657040699218114529135045123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-613729535413658853632012955840000000000000)
      constant := (22581547101402781204240288078844157812634440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 287 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel288
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116547720621430033543/25000000000000000000)
  centralHi := (466190882485720134173/100000000000000000000)
  directionLo := (467005190324617326979/100000000000000000000)
  directionHi := (23350259516230866349/5000000000000000000)

def endpointA : IntegerEndpointWitness 288 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree288.table
  base := (398333949921532347007444117877450065399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-68414716020810283636510720320000000000000)
      constant := (2456637581957010240273231870315098002615960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 288 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree288.table
  base := (3983339499215320318913338870156044838663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4311207518127180847236634843920000000000000)
      constant := (159213563879965881756673124639380230985472435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 288 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel289
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467005190324617326979/100000000000000000000)
  centralHi := (23350259516230866349/5000000000000000000)
  directionLo := (233909040370102832371/50000000000000000000)
  directionHi := (467818080740205664743/100000000000000000000)

def endpointA : IntegerEndpointWitness 289 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree289.table
  base := (1032872128431980676094427482660419508201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-68654410786390741919249516400000000000000)
      constant := (2474363818865960765404914974912566712131216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 289 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree289.table
  base := (4131488513727919942104557708073564111471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4326308288358749719049178996960000000000000)
      constant := (160360398135069659737163149319926023207310395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 289 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel290
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/50000000000000000000)
  centralHi := (467818080740205664743/100000000000000000000)
  directionLo := (468629561108523242083/100000000000000000000)
  directionHi := (117157390277130810521/25000000000000000000)

def endpointA : IntegerEndpointWitness 290 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree290.table
  base := (4280523356877938993053853859844500757763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-68894105551971200201988312480000000000000)
      constant := (2492153522780856073324774279239378003031052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 290 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree290.table
  base := (2140261678438968285850719619304808609311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4341409058590318590861723150000000000000000)
      constant := (161511332473392008308402929856659356218562390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 290 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel291
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468629561108523242083/100000000000000000000)
  centralHi := (117157390277130810521/25000000000000000000)
  directionLo := (469439638741856409171/100000000000000000000)
  directionHi := (117359909685464102293/25000000000000000000)

def endpointA : IntegerEndpointWitness 291 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree291.table
  base := (4430444021628207508202874817051000716287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-69133800317551658484727108560000000000000)
      constant := (2510006693673547504721209790698204002865148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 291 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree291.table
  base := (4430444021628205385717114994673980257591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4356509828821887462674267303040000000000000)
      constant := (162666366893208822089005683475143125163109795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 291 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel292
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469439638741856409171/100000000000000000000)
  centralHi := (117359909685464102293/25000000000000000000)
  directionLo := (470248320889508531773/100000000000000000000)
  directionHi := (235124160444754265887/50000000000000000000)

def endpointA : IntegerEndpointWitness 292 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree292.table
  base := (2290625250500405540432604008481687942989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-69373495083132116767465904640000000000000)
      constant := (2527923331516123390918383250147853503543912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 292 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree292.table
  base := (4581250501000809220376650761575106712063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4371610599053456334486811456080000000000000)
      constant := (163825501392810511373846551292777901144455435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 292 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel293
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470248320889508531773/100000000000000000000)
  centralHi := (235124160444754265887/50000000000000000000)
  directionLo := (235527807369278436683/50000000000000000000)
  directionHi := (471055614738556873367/100000000000000000000)

def endpointA : IntegerEndpointWitness 293 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree293.table
  base := (47329427880763847068743718240699524449/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-69613189848712575050204700720000000000000)
      constant := (2545903436280906271899628731046279809779600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 293 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree293.table
  base := (2366471394038191538029695240950387368677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4386711369285025206299355609120000000000000)
      constant := (164988735970501831738018472575497689810651730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 293 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel294
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/50000000000000000000)
  centralHi := (471055614738556873367/100000000000000000000)
  directionLo := (29491345463412363929/6250000000000000000)
  directionHi := (94372305482919564573/20000000000000000000)

def endpointA : IntegerEndpointWitness 294 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree294.table
  base := (610690109499178813309063380386691882917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-69852884614293033332943496800000000000000)
      constant := (2563947007940450156145914796612374140253344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 294 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree294.table
  base := (152672527374794658656036056894068904841/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-628830305645227725444557108880000000000000)
      constant := (23736581517800245171708180448745357173421920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 294 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel295
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29491345463412363929/6250000000000000000)
  centralHi := (94372305482919564573/20000000000000000000)
  directionLo := (94533213196496137303/20000000000000000000)
  directionHi := (118166516495620171629/25000000000000000000)

def endpointA : IntegerEndpointWitness 295 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree295.table
  base := (629873094743455368300906652405887094273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-70092579379873491615682292880000000000000)
      constant := (2582054046467537821524232005026988387016736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 295 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree295.table
  base := (5038984757947641693420091757671278959689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4416912909748162949924443915200000000000000)
      constant := (167327505353443109910872249980029463345123805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 295 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel296
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94533213196496137303/20000000000000000000)
  centralHi := (118166516495620171629/25000000000000000000)
  directionLo := (473469237447030257763/100000000000000000000)
  directionHi := (118367309361757564441/25000000000000000000)

def endpointA : IntegerEndpointWitness 296 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree296.table
  base := (5193334427191244137416905979129845552371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-70332274145453949898421088960000000000000)
      constant := (2600224551835178156477533538796519382209484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 296 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree296.table
  base := (5193334427191243039142334401592760111801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4432013679979731821736988068240000000000000)
      constant := (168503040155372807282644954968518226227391245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 296 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel297
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473469237447030257763/100000000000000000000)
  centralHi := (118367309361757564441/25000000000000000000)
  directionLo := (474271048753758374089/100000000000000000000)
  directionHi := (47427104875375837409/10000000000000000000)

def endpointA : IntegerEndpointWitness 297 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree297.table
  base := (1337142469258082255987480436623298438821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-70571968911034408181159885040000000000000)
      constant := (2618458524016603540783613223615972775021136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 297 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree297.table
  base := (5348569877032328061294541284460344893449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4447114450211300693549532221280000000000000)
      constant := (169682675028751291579323369692044784498895005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 297 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel298
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474271048753758374089/100000000000000000000)
  centralHi := (47427104875375837409/10000000000000000000)
  directionLo := (47507150678956466531/10000000000000000000)
  directionHi := (475071506789564665311/100000000000000000000)

def endpointA : IntegerEndpointWitness 298 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree298.table
  base := (5504691100834220286935129283952154691547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-70811663676614866463898681120000000000000)
      constant := (2636755962985267265166186374535808618766188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 298 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree298.table
  base := (2752345550417109721580314616744121360281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4462215220442869565362076374320000000000000)
      constant := (170866409971952576858312053773276619466537690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 298 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel299
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47507150678956466531/10000000000000000000)
  centralHi := (475071506789564665311/100000000000000000000)
  directionLo := (475870618383426693333/100000000000000000000)
  directionHi := (237935309191713346667/50000000000000000000)

def endpointA : IntegerEndpointWitness 299 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree299.table
  base := (5661698092014832784228604664079603240987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-71051358442195324746637477200000000000000)
      constant := (2655116868714840989056677295846318412963948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 299 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree299.table
  base := (5661698092014832044661437535390889948809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-4477315990674438437174620527360000000000000)
      constant := (172054244983364052260291612837458768037458205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 299 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel299
