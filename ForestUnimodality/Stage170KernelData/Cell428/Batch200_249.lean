import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell428.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch200_249
import ForestUnimodality.BinomialMassData.Q9_35.Batch200_249

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel200
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
  base := (-93745530705016085778889060131359261733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2957422420909470113514760884000000000000)
      constant := (72884190237122374151337990139868640738267) }

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
  base := (-468727653597984882823403717740475740659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-745538585000561090133930342780000000000000)
      constant := (18906703092465253111653179164230716688707709) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel201
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
  base := (-320196964076476243011359507204842614197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14862005289824996683012425585000000000000)
      constant := (368275621549357018348896315243420157385803) }

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
  base := (-320196964140473304957727902531472852521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-749313201538554454352036849496000000000000)
      constant := (19106176325946557463259650203897157830226471) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel202
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
  base := (-85122812326342350461647445700967465833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14936898475102642798451046750000000000000)
      constant := (372150435859396764826167313901098065068334) }

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
  base := (-170245624708861352509803646793697123687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-753087818076547818570143356212000000000000)
      constant := (19306689786957791026876735947447908840939337) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel203
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
  base := (-18873650071254067737520948472014281773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15011791660380288913889667915000000000000)
      constant := (376045394100913561923395677177152985718227) }

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
  base := (-589801566267650549385308471670438441/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-27030801236233613671008923676000000000000)
      constant := (696722981241889301024696505277686455447304) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel204
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
  base := (133918945027297723609602052276442470511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15086684845657935029328289080000000000000)
      constant := (379960496259266891707645044802276442470511) }

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
  base := (66959472492007358936450232499970954407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-380318525576267273503178184822000000000000)
      constant := (9855418694337252995594008474930098576765943) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel205
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
  base := (72033036544134532035651579081052029977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15161578030935581144766910245000000000000)
      constant := (383895742319990321633939948981949208119908) }

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
  base := (288132146138546896881143947156203320103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-764411667690527911224462876360000000000000)
      constant := (19914471527953757526874811926400653962685047) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel206
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
  base := (11094148477030948665122873835254925051/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3047294243242645452041106282000000000000)
      constant := (77570226453757724500604762565182039400408) }

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
  base := (443765939047892266622066936368605480313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-768186284228521275442569383076000000000000)
      constant := (20119145891910193202563592729085261668535337) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel207
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
  base := (24032812384582020677398375544865782797/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3062272880298174675128830515000000000000)
      constant := (78365333218306989530567013551849328913985) }

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
  base := (600820309585282982416592893025365975593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-771960900766514639660675889792000000000000)
      constant := (20324860479851601393865084607473042932804057) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel208
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
  base := (759295243815250527298211368117667104469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15386257586768519491082773740000000000000)
      constant := (395822343774268071771539185528117667104469) }

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
  base := (759295243789562949703358712128845693869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-775735517304508003878782396508000000000000)
      constant := (20531615291093885452145780769419113438999581) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel209
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
  base := (5744942049281443075245670864284237937/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3092230154409233121304278981000000000000)
      constant := (79967633060637937554696160515782095613984) }

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
  base := (229797681965621466899204775104209824731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-194877533460625342024222225806000000000000)
      constant := (5184852581240232827165572373888406281411819) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel210
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
  base := (1080506748185856182974655466427893723033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15536043957323811721960016070000000000000)
      constant := (403874130664661760230476327078927893723033) }

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
  base := (1080506748166069686001712931083026960503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-111897821482927818902142201420000000000000)
      constant := (2992606511540639691851420427237581188723521) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel211
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
  base := (1243243291237371157235687774908949472771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15610937142601457837398637235000000000000)
      constant := (407930239845203933899657191050533949472771) }

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
  base := (248648658244001206936274391491045796059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-787059366918488096533101916656000000000000)
      constant := (21158121057903989944897144510660506220034455) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel212
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
  base := (281480068742872593910313206674581141147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3137166065575820790567451680000000000000)
      constant := (82401298566298199187150511252674581141147) }

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
  base := (175925042962390403409557144168738000481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-197708495864120365187802105843000000000000)
      constant := (5342259188916633550460571610815736324047138) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel213
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
  base := (314595578488855140302291332295005866847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3152144702631350013655175913000000000000)
      constant := (83220577922070078084070317827420005866847) }

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
  base := (1572977892430901486093561072100999373449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-794608599994474824969314930088000000000000)
      constant := (21580992673426657144688391823583748969299001) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel214
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
  base := (434993981101193970801451361003222187499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15835616698434396183714500730000000000000)
      constant := (420219430168759783883544735456512888749996) }

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
  base := (1739975924393039074734816943970997922731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-798383216532468189187421436804000000000000)
      constant := (21793988810546265988351965179905778898213819) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel215
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
  base := (477098606680341930912754396242563428361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-15910509883712042299153121895000000000000)
      constant := (424356114493844680534348400425595253713444) }

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
  base := (954197213355534032615622017655310329961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-401078916535230776702763971760000000000000)
      constant := (11004012583197255902181263228140110206168089) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel216
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
  base := (103911669333252840294063884952104444403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3197080613797937682918348612000000000000)
      constant := (85702588514575217191159353731808417777612) }

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
  base := (2078233386656018504579315358018385077169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-805932449608454917623634450236000000000000)
      constant := (22223101740347675065022902830290100868781281) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel217
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
  base := (1124746395825030520201884863125447237147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16060296254267334530030364225000000000000)
      constant := (432689914393268218058397024096875894474294) }

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
  base := (2249492791642129782300401813236602487047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-115672438020921183120248708136000000000000)
      constant := (3205602647398436214345663068013056217409329) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel218
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
  base := (605543157307891926783461185444649687441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16135189439544980645468985390000000000000)
      constant := (436887029942576264122064517814278598749764) }

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
  base := (2422172629224608036102772193371434960957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-813481682684441646059847463668000000000000)
      constant := (22656375540108852211300447564512000313086893) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel219
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
  base := (2596272887103535450926393597343162080657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16210082624822626760907606555000000000000)
      constant := (441104289208494182791654140662968162080657) }

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
  base := (649068221774357116720357450023704398013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-204314074805608752569488492596000000000000)
      constant := (5718643191176018995627294064333461515502637) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel220
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
  base := (2771793553096540129534399182121611592421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16284975810100272876346227720000000000000)
      constant := (445341692178852549924918875532121611592421) }

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
  base := (554358710618236293452762171018163960647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-821030915760428374496060477100000000000000)
      constant := (23093810204978423743284571929419450170358515) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel221
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
  base := (2948734615175663445227731937802881323301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16359868995377918991784848885000000000000)
      constant := (449599238841616447224128592863427881323301) }

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
  base := (2948734615170961499659287179125540607213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-824805532298421738714166983816000000000000)
      constant := (23314087860342185122284693799986351489753437) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel222
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
  base := (625419212287684664527263021426742083029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3286952436131113021444694010000000000000)
      constant := (90775385836976678522782643179926742083029) }

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
  base := (1563548030717148845264131082823001552691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-414290074418207551466136745266000000000000)
      constant := (11767702865106069523353050817656727076081859) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel223
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
  base := (1653438940056372512729532780695811202267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16509655365933211222662091215000000000000)
      constant := (458174763196881311357971661512016622404534) }

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
  base := (1653438940054562568580063961267938339289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-416177382687204233575189998624000000000000)
      constant := (11878881907005727168157987824343528978625161) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel224
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
  base := (3488080059554972033797186392929461631957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16584548551210857338100712380000000000000)
      constant := (462492740865966546936405132792929461631957) }

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
  base := (3488080059551795951923747592085439713429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-119447054558914547338355214852000000000000)
      constant := (3425880301595656034945770019154198077994003) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel225
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
  base := (3670702588247915731883501217380572282807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16659441736488503453539333545000000000000)
      constant := (466830862180621910733446453358005572282807) }

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
  base := (3670702588245129096578114984939281944723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-839903998450395195586593010680000000000000)
      constant := (24205600621122210900745535788212024815291427) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel226
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
  base := (770949090959788596616091169316297893859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3346866984353229913795590942000000000000)
      constant := (94237825425890953922491613803816297893859) }

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
  base := (1927372727398249042994907291049726479031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-421839307494194279902349758698000000000000)
      constant := (12215539671655535803459937625327036597472519) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel227
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
  base := (2020104323969050347577943357179646205467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16809228107043795684416575875000000000000)
      constant := (475567535701195170481207816209984292410934) }

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
  base := (2020104323967977833219934938061264895243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-423726615763190962011403012056000000000000)
      constant := (12328799138591973473855589336270401979866907) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel228
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
  base := (528386519564534563009982069479045634577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16884121292321441799855197040000000000000)
      constant := (479966087884694000975665757665832365076616) }

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
  base := (2113546078257197299336350067074151968159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-425613924032187644120456265414000000000000)
      constant := (12442578711097265334197961298981033446439791) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel229
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
  base := (1103848992375848682258008463462619267339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-16959014477599087915293818205000000000000)
      constant := (484384783668921185415011561869475477069356) }

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
  base := (4415395969501743700054041979194332086491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-855002464602368652459019037544000000000000)
      constant := (25113756777802349281025028121445722272238059) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel230
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
  base := (4605120075986646774858111484155182146353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17033907662876734030732439370000000000000)
      constant := (488823623042963915204090921696655182146353) }

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
  base := (1151280018996299580887455739641015359603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-214694270285090504169281386065000000000000)
      constant := (6335849085868168839473456423202409752620547) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel231
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
  base := (4796264465168755181053582190142629719743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17108800848154380146171060535000000000000)
      constant := (493282605996024912882399329890767629719743) }

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
  base := (479626446516748447389865065284614385577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-61610835548453955778230860784000000000000)
      constant := (1826719722762603033802464791678761503495195) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel232
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
  base := (199553165054650821535950869974566319337/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3436738806686405252321936340000000000000)
      constant := (99552346503484145808143422445872831596685) }

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
  base := (997765825273031156647752689974838696709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-866326314216348745113338557692000000000000)
      constant := (25805796102890161755021845974528635480693705) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel233
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
  base := (5182814049007900515722766628165638844159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17258587218709672377048302865000000000000)
      constant := (502261002596580071347873355178790638844159) }

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
  base := (323925878062932661854108419609218194829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-217525232688585527332861266102000000000000)
      constant := (6509639073898960002455631365182106766186484) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel234
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
  base := (215128768905314810396533318996646999287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3466696080797463698497384806000000000000)
      constant := (101356083244608432990151164977483234996435) }

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
  base := (268910961131600619135759297708295741459/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-218468886823083868387387892781000000000000)
      constant := (6568089174070224846155947749019332456657455) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel235
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
  base := (5575044636889313452316911627353169266911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17408373589264964607925545195000000000000)
      constant := (511319973386455143530710962192978169266911) }

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
  base := (348440289805535056230313400155878942331/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-219412540957582209441914519460000000000000)
      constant := (6626799326109524632638309886228052272696876) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel236
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
  base := (1443322570383173330994910300313298872583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17483266774542610723364166360000000000000)
      constant := (515879674076574470318784905711253195490332) }

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
  base := (2886645140766016587962369146681757079897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-440712390184161100992882292278000000000000)
      constant := (13371539059782727617171498750365006096914953) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel237
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
  base := (5972956146424252950976442933702376190809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17558159959820256838802787525000000000000)
      constant := (520459518283261388391052576679327376190809) }

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
  base := (746619518302959233866658845791408250089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-221299849226578891550967772818000000000000)
      constant := (6744999785291542621077127901842258008508722) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel238
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
  base := (6174042221529494169189748654410505056529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17633053145097902954241408690000000000000)
      constant := (525059505996481399583396406926910505056529) }

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
  base := (246961688861159448405944798177226954289/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-126996287634901275774568228284000000000000)
      constant := (3888280052678364848356606323335414717000575) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel239
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
  base := (255061939876667378620877312573778368079/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3541589266075109813936005971000000000000)
      constant := (105935927441260554276543754180993891840395) }

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
  base := (1275309699383247779974385829572110380607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-892748629982302294640084104704000000000000)
      constant := (27456961801825950763514951489886367043248715) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel240
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
  base := (6580474962755391219538084534602163285321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17782839515653195185118651020000000000000)
      constant := (534319911902895071168584757734602163285321) }

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
  base := (6580474962755000389725012604465759286363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-896523246520295658858190611420000000000000)
      constant := (27697003439916669813396102185618822205031787) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel241
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
  base := (6785821609315042686088830421283296780699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17857732700930841300557272185000000000000)
      constant := (538980330076527727195844994021908296780699) }

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
  base := (6785821609314699873544575369196942451959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-900297863058289023076297118136000000000000)
      constant := (27938085282543913118637694897747850180145991) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel242
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
  base := (874073553370439390679121758804903200213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-17932625886208487415995893350000000000000)
      constant := (543660891717568615724758283362939225601704) }

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
  base := (6992588426963214435543285235685352956617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-904072479596282387294403624852000000000000)
      constant := (28180207329235706656366150348161382294874233) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel243
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
  base := (1800193851541436375739095592458390963219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18007519071486133531434514515000000000000)
      constant := (548361596816482673720710492645458563852876) }

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
  base := (3600387703082740882053347781177654680497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-453923548067137875756255065784000000000000)
      constant := (14211684789762416186656180325711105079344353) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel244
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
  base := (1852595634370592298892282388479502140311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18082412256763779646873135680000000000000)
      constant := (553082445363830536560611696103918008561244) }

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
  base := (3705191268741068935273684908577144858901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-455810856336134557865308319142000000000000)
      constant := (14333786016474380717015320708729880098086149) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel245
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
  base := (7621409811568382156536730790046419312393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18157305442041425762311756845000000000000)
      constant := (557823437350267200197727408905671419312393) }

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
  base := (3810704905784089632391098069397016453417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-65385452086447319996337367500000000000000)
      constant := (2065201049217827761964780011790779115173919) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel246
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
  base := (7833857219171827004588269516664055716927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18232198627319071877750378010000000000000)
      constant := (562584572766540707250786714489164055716927) }

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
  base := (7833857219171649053960222782329119569867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-919170945748255844166829651716000000000000)
      constant := (29159097547373968185991500258753326858923483) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel247
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
  base := (402386237556625125847061195092685970929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3661418362519343598637799835000000000000)
      constant := (113473170320698171299401418204495743883716) }

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
  base := (8047724751132346443842838088192938565729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-922945562286249208384936158432000000000000)
      constant := (29406420607473050150566689727188253989720721) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel248
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
  base := (8263012398380696019175412378425580473121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18381984997874364108627620340000000000000)
      constant := (572167273852047935261968356938425580473121) }

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
  base := (8263012398380559136010966700294935117519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-926720178824242572603042665148000000000000)
      constant := (29654783868902418658609953877927251820758431) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel249
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
  base := (4239860075967969088915654404981145321251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18456878183152010224066241505000000000000)
      constant := (576988839503231474212210986100587290642502) }

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
  base := (8479720151935818126899426211198115377289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-930494795362235936821149171864000000000000)
      constant := (29904187331222030728946598773005907653487161) }

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
end ForestUnimodality.Stage170KernelData.Cell428.Kernel249
