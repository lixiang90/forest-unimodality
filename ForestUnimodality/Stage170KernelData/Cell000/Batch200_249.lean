import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell000.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch200_249
import ForestUnimodality.BinomialMassData.Q9_35.Batch200_249

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel200
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96973565247465633293/25000000000000000000)
  centralHi := (387894260989862533173/100000000000000000000)
  directionLo := (194436279141901090253/50000000000000000000)
  directionHi := (388872558283802180507/100000000000000000000)

def endpointA : IntegerEndpointWitness 200 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree200.table
  base := (-2791919473573273746796387127504704528713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-47321576649729954755496665280000000000000)
      constant := (1145269648795620134106481766979962363770296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 200 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree200.table
  base := (-1116767789493845609298154615311797812561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2982339737749120127732749376400000000000000)
      constant := (74348327636899162090352655748243047679612775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 200 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel201
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194436279141901090253/50000000000000000000)
  centralHi := (388872558283802180507/100000000000000000000)
  directionLo := (6091381259638094593/1562500000000000000)
  directionHi := (389848400616838053953/100000000000000000000)

def endpointA : IntegerEndpointWitness 201 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree201.table
  base := (-1378419987314328454507021409211504961327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-47561271415310413038235461360000000000000)
      constant := (1157410640795307114782957037282615920618768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 201 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree201.table
  base := (-2756839974770284812822566253786211911977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2997440507980688999545293529440000000000000)
      constant := (75134345480128373148395586061252756163131270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 201 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6091381259638094593/1562500000000000000)
  centralHi := (389848400616838053953/100000000000000000000)
  directionLo := (390821806378334255877/100000000000000000000)
  directionHi := (195410903189167127939/50000000000000000000)

def endpointA : IntegerEndpointWitness 202 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree202.table
  base := (-1088526829537595461372534205389811498757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-47800966180890871320974257440000000000000)
      constant := (1169615103701109621372519910572203770024860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 202 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree202.table
  base := (-1088526829587323884144686470664365937621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3012541278212257871357837682480000000000000)
      constant := (75924463645460434117717519469148151726414275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 202 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390821806378334255877/100000000000000000000)
  centralHi := (195410903189167127939/50000000000000000000)
  directionLo := (391792793729213099901/100000000000000000000)
  directionHi := (195896396864606549951/50000000000000000000)

def endpointA : IntegerEndpointWitness 203 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree203.table
  base := (-83917211866867161321491937822617339519/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-48040660946471329603713053520000000000000)
      constant := (1181883037444863812417254572467409961083136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 203 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree203.table
  base := (-335668847481109466435894711490513633429/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-432520292634832391881483119360000000000000)
      constant := (10959811732674350480094648356181312365279760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 203 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel204
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391792793729213099901/100000000000000000000)
  centralHi := (195896396864606549951/50000000000000000000)
  directionLo := (392761380605908422889/100000000000000000000)
  directionHi := (39276138060590842289/10000000000000000000)

def endpointA : IntegerEndpointWitness 204 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree204.table
  base := (-529788220146915432657356893335695484171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-48280355712051787886451849600000000000000)
      constant := (1194214441959220578095532845706572180633160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 204 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree204.table
  base := (-5297882201660728231458411767016096080547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3042742818675395614982925988560000000000000)
      constant := (77517000925783424069860788742489056460265985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 204 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel205
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392761380605908422889/100000000000000000000)
  centralHi := (39276138060590842289/10000000000000000000)
  directionLo := (78745516944846273657/20000000000000000000)
  directionHi := (196863792362115684143/50000000000000000000)

def endpointA : IntegerEndpointWitness 205 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree205.table
  base := (-5224176090293938863831479739409424222599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-48520050477632246169190645680000000000000)
      constant := (1206609317177631944203456514392362303109604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 205 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree205.table
  base := (-5224176090462090986833399916609312869691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3057843588906964486795470141600000000000000)
      constant := (78319420032573393636451139005430718346925705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 205 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel206
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78745516944846273657/20000000000000000000)
  centralHi := (196863792362115684143/50000000000000000000)
  directionLo := (394691423583150997753/100000000000000000000)
  directionHi := (197345711791575498877/50000000000000000000)

def endpointA : IntegerEndpointWitness 206 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree206.table
  base := (-5149583242393886702574214324071313774347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-48759745243212704451929441760000000000000)
      constant := (1219067663034337771676125586983714744902612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 206 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree206.table
  base := (-5149583242541477272056446544301738395547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3072944359138533358608014294640000000000000)
      constant := (79125939445062650862409083437734074093090985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 206 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394691423583150997753/100000000000000000000)
  centralHi := (197345711791575498877/50000000000000000000)
  directionLo := (98913228617123003377/25000000000000000000)
  directionHi := (395652914468492013509/100000000000000000000)

def endpointA : IntegerEndpointWitness 207 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree207.table
  base := (-5074103674015327171891486904259317762583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-48999440008793162734668237840000000000000)
      constant := (1231589479464352743197181206612962728949668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 207 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree207.table
  base := (-507410367414486756551970689661825138263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3088045129370102230420558447680000000000000)
      constant := (79936559159270930530528544004000528411255650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 207 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98913228617123003377/25000000000000000000)
  centralHi := (395652914468492013509/100000000000000000000)
  directionLo := (79322414891310360349/20000000000000000000)
  directionHi := (198306037228275900873/50000000000000000000)

def endpointA : IntegerEndpointWitness 208 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree208.table
  base := (-2498868700607033881629060965813185553711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-49239134774373621017407033920000000000000)
      constant := (1244174766403453628800724075473494515570312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 208 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree208.table
  base := (-999547480265552599722869384356933424039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3103145899601671102233102600720000000000000)
      constant := (80751279171264634863618685046914756555552225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 208 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79322414891310360349/20000000000000000000)
  centralHi := (198306037228275900873/50000000000000000000)
  directionLo := (397568920417638938271/100000000000000000000)
  directionHi := (12424028763051216821/3125000000000000000)

def endpointA : IntegerEndpointWitness 209 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree209.table
  base := (-4920484439858509923032709413858391891533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-49478829539954079300145830000000000000000)
      constant := (1256823523788166822701319833534566432433868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 209 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree209.table
  base := (-1230121109989573995088149721159932278567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3118246669833239974045646753760000000000000)
      constant := (81570099477156071421471509661591266367004340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 209 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397568920417638938271/100000000000000000000)
  centralHi := (12424028763051216821/3125000000000000000)
  directionLo := (79704693803907046121/20000000000000000000)
  directionHi := (199261734509767615303/50000000000000000000)

def endpointA : IntegerEndpointWitness 210 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree210.table
  base := (-242117240281634945081245145953229671657/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-49718524305534537582884626080000000000000)
      constant := (1269535751555756143897329866523741626267440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 210 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree210.table
  base := (-4842344805720275506199445475540585230249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-447621062866401263694027272400000000000000)
      constant := (11770431439014672428599728155556079516941285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 210 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79704693803907046121/20000000000000000000)
  centralHi := (199261734509767615303/50000000000000000000)
  directionLo := (3195805893847066451/800000000000000000)
  directionHi := (49934467091360413297/12500000000000000000)

def endpointA : IntegerEndpointWitness 211 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree211.table
  base := (-4763318514039309450590154291936968329807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-49958219071114995865623422160000000000000)
      constant := (1282311449644210893382532367062252126680772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 211 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree211.table
  base := (-4763318514116168866301421820883198657423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3148448210296377717670735059840000000000000)
      constant := (83220040955306437113712546222851616328931365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 211 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel212
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3195805893847066451/800000000000000000)
  centralHi := (49934467091360413297/12500000000000000000)
  directionLo := (200212869912250847859/50000000000000000000)
  directionHi := (400425739824501695719/100000000000000000000)

def endpointA : IntegerEndpointWitness 212 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree212.table
  base := (-2341702790201284545478223339902795629079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-50197913836695454148362218240000000000000)
      constant := (1295150617992234161072815402560777634967368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 212 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree212.table
  base := (-292712848779376338096863851828716056653/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3163548980527946589483279212880000000000000)
      constant := (84051162120012870651536490104863433057920240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 212 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200212869912250847859/50000000000000000000)
  centralHi := (400425739824501695719/100000000000000000000)
  directionLo := (100343373595157323857/25000000000000000000)
  directionHi := (401373494380629295429/100000000000000000000)

def endpointA : IntegerEndpointWitness 213 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree213.table
  base := (-575325752483890076532134043066754708061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-50437608602275912431101014320000000000000)
      constant := (1308053256539231375810045803971863849342048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 213 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree213.table
  base := (-4602606019930315964177803533294466689731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3178649750759515461295823365920000000000000)
      constant := (84886383563510629320752804869934855661015905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 213 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100343373595157323857/25000000000000000000)
  centralHi := (401373494380629295429/100000000000000000000)
  directionLo := (201159508145050522417/50000000000000000000)
  directionHi := (80463803258020208967/20000000000000000000)

def endpointA : IntegerEndpointWitness 214 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree214.table
  base := (-452091984742082540154105964384724692731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-50677303367856370713839810400000000000000)
      constant := (1321019365225299092046027457864611012290760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 214 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree214.table
  base := (-904183969494554692500749071337627583629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3193750520991084333108367518960000000000000)
      constant := (85725705282130661492943487951259406210054475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 214 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel215
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201159508145050522417/50000000000000000000)
  centralHi := (80463803258020208967/20000000000000000000)
  directionLo := (80652464251491317509/20000000000000000000)
  directionHi := (201631160628728293773/50000000000000000000)

def endpointA : IntegerEndpointWitness 215 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree215.table
  base := (-1109586769464377286233357828598368198247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-50916998133436828996578606480000000000000)
      constant := (1334048943991214007036260273292426108828048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 215 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree215.table
  base := (-138698346184471758343419416608149160677/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3208851291222653204920911672000000000000000)
      constant := (86569127272245570089305404661992110580292320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 215 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80652464251491317509/20000000000000000000)
  centralHi := (201631160628728293773/50000000000000000000)
  directionLo := (404203424803983639443/100000000000000000000)
  directionHi := (101050856200995909861/25000000000000000000)

def endpointA : IntegerEndpointWitness 216 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree216.table
  base := (-4354887725819651390571013737970387529031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-51156692899017287279317402560000000000000)
      constant := (1347141992778422202588196944728118449883876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 216 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree216.table
  base := (-1088721931464913911633687111862578707221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3223952061454222076733455825040000000000000)
      constant := (87416649530268954148958075339622672866923420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 216 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404203424803983639443/100000000000000000000)
  centralHi := (101050856200995909861/25000000000000000000)
  directionLo := (202571171135348865649/50000000000000000000)
  directionHi := (405142342270697731299/100000000000000000000)

def endpointA : IntegerEndpointWitness 217 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree217.table
  base := (-533817725722627551369735180583011909637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-51396387664597745562056198640000000000000)
      constant := (1360298511529028605611821174051343618891616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 217 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree217.table
  base := (-1067635451454031201495999293569430806047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-462721833097970135506571425440000000000000)
      constant := (12609753150379251962387807674156279687153420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 217 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202571171135348865649/50000000000000000000)
  centralHi := (405142342270697731299/100000000000000000000)
  directionLo := (406079088821259944257/100000000000000000000)
  directionHi := (203039544410629972129/50000000000000000000)

def endpointA : IntegerEndpointWitness 218 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree218.table
  base := (-4185309332053254754520383037707413302123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-51636082430178203844794994720000000000000)
      constant := (1373518500185786661913427566849170346791508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 218 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree218.table
  base := (-2092654666042029413902179431902098771793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3254153601917359820358544131120000000000000)
      constant := (89123994835896667857370677919199971601821430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 218 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406079088821259944257/100000000000000000000)
  centralHi := (203039544410629972129/50000000000000000000)
  directionLo := (407013679444834208031/100000000000000000000)
  directionHi := (12719177482651069001/3125000000000000000)

def endpointA : IntegerEndpointWitness 219 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree219.table
  base := (-819838063757678566062516901761298617339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-51875777195758662127533790800000000000000)
      constant := (1386801958692088217856799859154774027653220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 219 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree219.table
  base := (-4099190318815422842804686189837985684449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3269254372148928692171088284160000000000000)
      constant := (89983817876527435053877979034857693507309995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 219 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel220
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407013679444834208031/100000000000000000000)
  centralHi := (12719177482651069001/3125000000000000000)
  directionLo := (50993266119860710609/12500000000000000000)
  directionHi := (407946128958885684873/100000000000000000000)

def endpointA : IntegerEndpointWitness 220 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree220.table
  base := (-401218477998135182617233848303068597603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-52115471961339120410272586880000000000000)
      constant := (1400148886991953604690586640467877256095880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 220 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree220.table
  base := (-125380774375158428324862015446576843531/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3284355142380497563983632437200000000000000)
      constant := (90847741171118326376660958757298837546716960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 220 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel221
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50993266119860710609/12500000000000000000)
  centralHi := (407946128958885684873/100000000000000000000)
  directionLo := (16355058080476868689/4000000000000000000)
  directionHi := (204438226005960858613/50000000000000000000)

def endpointA : IntegerEndpointWitness 221 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree221.table
  base := (-98107318236808930477495966959040484469/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-52355166726919578693011382960000000000000)
      constant := (1413559285030021920506787135916553522484960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 221 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree221.table
  base := (-122634147796661513070319020150341379657/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3299455912612066435796176590240000000000000)
      constant := (91715764716278500420799694143949323583489120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 221 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel222
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16355058080476868689/4000000000000000000)
  centralHi := (204438226005960858613/50000000000000000000)
  directionLo := (102451165771544193349/25000000000000000000)
  directionHi := (409804663086176773397/100000000000000000000)

def endpointA : IntegerEndpointWitness 222 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree222.table
  base := (-153420567237972963874786469578333423681/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-52594861492500036975750179040000000000000)
      constant := (1427033152751541504954303038922166657631900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 222 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree222.table
  base := (-1917757090483792243000666387925147248759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3314556682843635307608720743280000000000000)
      constant := (92587888508654430136924155531868677848108090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 222 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel223
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102451165771544193349/25000000000000000000)
  centralHi := (409804663086176773397/100000000000000000000)
  directionLo := (51341347062530347921/12500000000000000000)
  directionHi := (410730776500242783369/100000000000000000000)

def endpointA : IntegerEndpointWitness 223 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree223.table
  base := (-1872924573975095736018410708529321668967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-52834556258080495258488975120000000000000)
      constant := (1440570490102360601982914294481765426648264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 223 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree223.table
  base := (-1872924573983106698994809188812788340993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3329657453075204179421264896320000000000000)
      constant := (93464112544929331130390880855953733712913430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 223 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel224
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51341347062530347921/12500000000000000000)
  centralHi := (410730776500242783369/100000000000000000000)
  directionLo := (205827403205823108117/50000000000000000000)
  directionHi := (82330961282329243247/20000000000000000000)

def endpointA : IntegerEndpointWitness 224 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree224.table
  base := (-3655297643865210733160700865282075693407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-53074251023660953541227771200000000000000)
      constant := (1454171297028918206038383369978871697226372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 224 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree224.table
  base := (-731059528775853667140215849804663123623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-477822603329539007319115578480000000000000)
      constant := (13477776688831800167390828105068183953365975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 224 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205827403205823108117/50000000000000000000)
  centralHi := (82330961282329243247/20000000000000000000)
  directionLo := (6446511981552706427/1562500000000000000)
  directionHi := (412576766819373211329/100000000000000000000)

def endpointA : IntegerEndpointWitness 225 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree225.table
  base := (-3563859681939189343361977729908051727247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-53313945789241411823966567280000000000000)
      constant := (1467835573478235087268227554830367793091012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 225 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree225.table
  base := (-3563859681951523223545273724795287635203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3359858993538341923046353202400000000000000)
      constant := (95228861336089270649478561378425154529375265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 225 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel226
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/1562500000000000000)
  centralHi := (412576766819373211329/100000000000000000000)
  directionLo := (103374167891586009283/25000000000000000000)
  directionHi := (413496671566344037133/100000000000000000000)

def endpointA : IntegerEndpointWitness 226 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree226.table
  base := (-433941909409211357872645421914105658503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-53553640554821870106705363360000000000000)
      constant := (1481563319397904991431084803578748618927904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 226 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree226.table
  base := (-3471535275284512181792809648781072536113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3374959763769910794858897355440000000000000)
      constant := (96117386084519463704152875863056637228652315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 226 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103374167891586009283/25000000000000000000)
  centralHi := (413496671566344037133/100000000000000000000)
  directionLo := (207207267170919057631/50000000000000000000)
  directionHi := (414414534341838115263/100000000000000000000)

def endpointA : IntegerEndpointWitness 227 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree227.table
  base := (-1689162218414596170571963670075119883579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-53793335320402328389444159440000000000000)
      constant := (1495354534736086010330452438069399040931368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 227 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree227.table
  base := (-675664887367737283571472134328289573251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3390060534001479666671441508480000000000000)
      constant := (97010011063937869789942390144959845272767525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 227 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel228
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207207267170919057631/50000000000000000000)
  centralHi := (414414534341838115263/100000000000000000000)
  directionLo := (83066073736774162253/20000000000000000000)
  directionHi := (207665184341935405633/50000000000000000000)

def endpointA : IntegerEndpointWitness 228 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree228.table
  base := (-821056794856800022588012887831077144951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-54033030085982786672182955520000000000000)
      constant := (1509209219441492118716323330594702765680784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 228 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree228.table
  base := (-3284227179435529561589845907444788003809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3405161304233048538483985661520000000000000)
      constant := (97906736271203225417533629041188026939066795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 228 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83066073736774162253/20000000000000000000)
  centralHi := (207665184341935405633/50000000000000000000)
  directionLo := (416244187981523159631/100000000000000000000)
  directionHi := (26015261748845197477/6250000000000000000)

def endpointA : IntegerEndpointWitness 229 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree229.table
  base := (-797310878938081207162047343193048696593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-54272724851563244954921751600000000000000)
      constant := (1523127373463384873716526867698911220854512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 229 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree229.table
  base := (-3189243515759632421708773029449128747733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3420262074464617410296529814560000000000000)
      constant := (98807561703207805838790558171792963456805415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 229 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel230
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416244187981523159631/100000000000000000000)
  centralHi := (26015261748845197477/6250000000000000000)
  directionLo := (417156005477225657133/100000000000000000000)
  directionHi := (208578002738612828567/50000000000000000000)

def endpointA : IntegerEndpointWitness 230 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree230.table
  base := (-3093373458354317145546789380397744907523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-54512419617143703237660547680000000000000)
      constant := (1537108996751565272973005255078409020369908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 230 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree230.table
  base := (-77334336459018202825933691035238118231/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3435362844696186282109073967600000000000000)
      constant := (99712487356876926440581492163854666441336200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 230 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417156005477225657133/100000000000000000000)
  centralHi := (208578002738612828567/50000000000000000000)
  directionLo := (104516458567249306621/25000000000000000000)
  directionHi := (83613166853799445297/20000000000000000000)

def endpointA : IntegerEndpointWitness 231 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree231.table
  base := (-2996617019650064220543426913429639272739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-54752114382724161520399343760000000000000)
      constant := (1551154089256365767767776191376281442909044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 231 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree231.table
  base := (-1498308509827844238815371276240239157921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-492923373561107879131659731520000000000000)
      constant := (14374501889881207660228987668447183258945530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 231 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104516458567249306621/25000000000000000000)
  centralHi := (83613166853799445297/20000000000000000000)
  directionLo := (104743421828160105293/25000000000000000000)
  directionHi := (418973687312640421173/100000000000000000000)

def endpointA : IntegerEndpointWitness 232 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree232.table
  base := (-2898974211925548696688053501748164406633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-54991809148304619803138139840000000000000)
      constant := (1565262650928642427528639870473007342373468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 232 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree232.table
  base := (-2898974211930482697246850497354754764279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3465564385159324025734162273680000000000000)
      constant := (101534639317072324932324138997620085082751645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 232 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104743421828160105293/25000000000000000000)
  centralHi := (418973687312640421173/100000000000000000000)
  directionLo := (104969894355973478061/25000000000000000000)
  directionHi := (83975915484778782449/20000000000000000000)

def endpointA : IntegerEndpointWitness 233 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree233.table
  base := (-2800445047337770586298987559129327699651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-55231503913885078085876935920000000000000)
      constant := (1579434681719767252206323018713482689201396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 233 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree233.table
  base := (-280044504734209896981723699453742966103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3480665155390892897546706426720000000000000)
      constant := (102451865617610078264251934567290329733047650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 233 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104969894355973478061/25000000000000000000)
  centralHi := (83975915484778782449/20000000000000000000)
  directionLo := (52597939660067908583/12500000000000000000)
  directionHi := (84156703456108653733/20000000000000000000)

def endpointA : IntegerEndpointWitness 234 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree234.table
  base := (-2701029537916633061414243600599069375281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-55471198679465536368615732000000000000000)
      constant := (1593670181581620629112673578037603722498876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 234 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree234.table
  base := (-1350514768960215049316266113429096862207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3495765925622461769359250579760000000000000)
      constant := (103373192127834389880580095993347742537518570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 234 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel235
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52597939660067908583/12500000000000000000)
  centralHi := (84156703456108653733/20000000000000000000)
  directionLo := (105421379856122753679/25000000000000000000)
  directionHi := (421685519424491014717/100000000000000000000)

def endpointA : IntegerEndpointWitness 235 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree235.table
  base := (-162545480972924559868406895921603940637/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-55710893445045994651354528080000000000000)
      constant := (1607969150466583930904248793611017347799232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 235 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree235.table
  base := (-162545480973132738734165128908452609827/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3510866695854030641171794732800000000000000)
      constant := (104298618844828621085975416338078865769478160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 235 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel236
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105421379856122753679/25000000000000000000)
  centralHi := (421685519424491014717/100000000000000000000)
  directionLo := (211292798131893460289/50000000000000000000)
  directionHi := (422585596263786920579/100000000000000000000)

def endpointA : IntegerEndpointWitness 236 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree236.table
  base := (-62488488301736919982994436382748858529/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-55950588210626452934093324160000000000000)
      constant := (1622331588327532251486728706658760182635360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 236 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree236.table
  base := (-2499539532072398670746876716677029124029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3525967466085599512984338885840000000000000)
      constant := (105228145765706373338729004598782127864612895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 236 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel237
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211292798131893460289/50000000000000000000)
  centralHi := (422585596263786920579/100000000000000000000)
  directionLo := (423483760074619455831/100000000000000000000)
  directionHi := (52935470009327431979/12500000000000000000)

def endpointA : IntegerEndpointWitness 237 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree237.table
  base := (-95898602363370524988330420033442660629/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-56190282976206911216832120240000000000000)
      constant := (1636757495117827276704040455026655733937100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 237 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree237.table
  base := (-1198732529543413091144168491356291320129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3541068236317168384796883038880000000000000)
      constant := (106161772887611051613830361081067417253136790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 237 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel238
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423483760074619455831/100000000000000000000)
  centralHi := (52935470009327431979/12500000000000000000)
  directionLo := (10609500575081732751/2500000000000000000)
  directionHi := (424380023003269310041/100000000000000000000)

def endpointA : IntegerEndpointWitness 238 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree238.table
  base := (-71703259004713496338101656656325061739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-56429977741787369499570916320000000000000)
      constant := (1651246870791310286761146864547990392097408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 238 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree238.table
  base := (-2294504288153080152844151967772923114057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-508024143792676750944203884560000000000000)
      constant := (15299928601102205118664795593383947691008005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 238 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel239
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10609500575081732751/2500000000000000000)
  centralHi := (424380023003269310041/100000000000000000000)
  directionLo := (425274397068025859809/100000000000000000000)
  directionHi := (42527439706802585981/10000000000000000000)

def endpointA : IntegerEndpointWitness 239 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree239.table
  base := (-2190657230690681635155098897899622305163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-56669672507367827782309712400000000000000)
      constant := (1665799715302295287412038559598401510779348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 239 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree239.table
  base := (-2190657230692653746758060540764438891213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3571269776780306128421971344960000000000000)
      constant := (108041327723221260163934412793760712471652815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 239 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel240
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425274397068025859809/100000000000000000000)
  centralHi := (42527439706802585981/10000000000000000000)
  directionLo := (85233378832213487537/20000000000000000000)
  directionHi := (213083447080533718843/50000000000000000000)

def endpointA : IntegerEndpointWitness 240 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree240.table
  base := (-1042961949004407644940131872132624748659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-56909367272948286065048508480000000000000)
      constant := (1680416028605562267024057677822939002010728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 240 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree240.table
  base := (-1042961949005272568017868151627962333531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3586370547011875000234515498000000000000000)
      constant := (108987255431358800061531501968902298456569810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 240 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel241
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85233378832213487537/20000000000000000000)
  centralHi := (213083447080533718843/50000000000000000000)
  directionLo := (85411505210061247017/20000000000000000000)
  directionHi := (213528763025153117543/50000000000000000000)

def endpointA : IntegerEndpointWitness 241 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree241.table
  base := (-990152150647697534774258453030824804381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-57149062038528744347787304560000000000000)
      constant := (1695095810656350576706989141805753401564952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 241 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree241.table
  base := (-1980304301296912387201351801043084669059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3601471317243443872047059651040000000000000)
      constant := (109937283329386466797146414405392444256080545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 241 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel242
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85411505210061247017/20000000000000000000)
  centralHi := (213528763025153117543/50000000000000000000)
  directionLo := (427946304381198648859/100000000000000000000)
  directionHi := (21397315219059932443/5000000000000000000)

def endpointA : IntegerEndpointWitness 242 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree242.table
  base := (-1873798451627367396909308588677686332443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-57388756804109202630526100640000000000000)
      constant := (1709839061410352430769835150725289254670228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 242 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree242.table
  base := (-374759690325739655223320912236546263449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3616572087475012743859603804080000000000000)
      constant := (110891411414590409390693034209102230827274975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 242 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel243
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427946304381198648859/100000000000000000000)
  centralHi := (21397315219059932443/5000000000000000000)
  directionLo := (428833240678521859347/100000000000000000000)
  directionHi := (107208310169630464837/25000000000000000000)

def endpointA : IntegerEndpointWitness 243 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree243.table
  base := (-353281271994011672985774033549246023401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-57628451569689660913264896720000000000000)
      constant := (1724645780823706524840730779079015079531980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 243 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree243.table
  base := (-1766406359971225695691325455162053731987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3631672857706581615672147957120000000000000)
      constant := (111849639684284123733408452816517296835663185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 243 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel244
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428833240678521859347/100000000000000000000)
  centralHi := (107208310169630464837/25000000000000000000)
  directionLo := (214859173174058703287/50000000000000000000)
  directionHi := (17188733853924696263/4000000000000000000)

def endpointA : IntegerEndpointWitness 244 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree244.table
  base := (-1658128037178740439733710033820683083093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-57868146335270119196003692800000000000000)
      constant := (1739515968852991769055169993304717267667628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 244 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree244.table
  base := (-1658128037179764304134006267451078238347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3646773627938150487484692110160000000000000)
      constant := (112811968135808068759031589740442485831604985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 244 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel245
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214859173174058703287/50000000000000000000)
  centralHi := (17188733853924696263/4000000000000000000)
  directionLo := (53825204084825313853/12500000000000000000)
  directionHi := (17224065307144100433/4000000000000000000)

def endpointA : IntegerEndpointWitness 245 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree245.table
  base := (-309792698800034205627857334255360621453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-58107841100850577478742488880000000000000)
      constant := (1754449625455221133785890959464892787570940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 245 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree245.table
  base := (-1548963494001069044474860436926749139837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-523124914024245622756748037600000000000000)
      constant := (16254056680932755643788577526907563780105705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 245 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel246
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53825204084825313853/12500000000000000000)
  centralHi := (17224065307144100433/4000000000000000000)
  directionLo := (215741555421524931947/50000000000000000000)
  directionHi := (86296622168609972779/20000000000000000000)

def endpointA : IntegerEndpointWitness 246 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree246.table
  base := (-287782548214820705015599095414104396793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-58347535866431035761481284960000000000000)
      constant := (1769446750587835605453164095971717912064140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 246 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree246.table
  base := (-1438912741074891149858825211080287142113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3676975168401288231109780416240000000000000)
      constant := (114748925573841046923753302034613329650182315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 246 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel247
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215741555421524931947/50000000000000000000)
  centralHi := (86296622168609972779/20000000000000000000)
  directionLo := (86472558380127319629/20000000000000000000)
  directionHi := (216181395950318299073/50000000000000000000)

def endpointA : IntegerEndpointWitness 247 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree247.table
  base := (-1327975788934771440244111700160776231911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-58587230632011494044220081040000000000000)
      constant := (1784507344208698250018212301829356895072356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 247 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree247.table
  base := (-1327975788935462233209042917891175104697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3692075938632857102922324569280000000000000)
      constant := (115723554555162454265565197908868662099349235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 247 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel248
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86472558380127319629/20000000000000000000)
  centralHi := (216181395950318299073/50000000000000000000)
  directionLo := (216620343399131560881/50000000000000000000)
  directionHi := (433240686798263121763/100000000000000000000)

def endpointA : IntegerEndpointWitness 248 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree248.table
  base := (-1216152648012346187873218171661744851123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-58826925397591952326958877120000000000000)
      constant := (1799631406276088381824093245713353020595508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 248 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree248.table
  base := (-304038162003238011137183308325329237359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3707176708864425974734868722320000000000000)
      constant := (116702283707938119943200041490513177347388180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 248 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel249
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216620343399131560881/50000000000000000000)
  centralHi := (433240686798263121763/100000000000000000000)
  directionLo := (217058403186071245273/50000000000000000000)
  directionHi := (434116806372142490547/100000000000000000000)

def endpointA : IntegerEndpointWitness 249 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree249.table
  base := (-551721664317184554295033538554722183003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-59066620163172410609697673200000000000000)
      constant := (1814818936748695835508307918881562222535976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 249 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree249.table
  base := (-137930416079362558045327157029890633579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-3722277479095994846547412875360000000000000)
      constant := (117685113029637796685939076110309414358185160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 249 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel249
