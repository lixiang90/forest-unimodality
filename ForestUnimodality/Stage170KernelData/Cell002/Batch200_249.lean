import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell002.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch200_249
import ForestUnimodality.BinomialMassData.Q9_35.Batch200_249

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel200
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
  base := (-3905125797761531051838601955817259126643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17443083693335905311194711220000000000000)
      constant := (414700037483296044347678853176730963493428) }

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
  base := (-976281449550374698207420247301738976233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1099317231296295917101005223225000000000000)
      constant := (26948738801110604989332287740644295803291660) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel201
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
  base := (-3895643186599746561407457484714040455443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17531450422134395930595651680000000000000)
      constant := (419109784692376969964627226423643838178228) }

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
  base := (-7791286373967321394673122145149485930347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2209768670421201652246528944410000000000000)
      constant := (54468918770248295522285302162120375947064985) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel202
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
  base := (-3885919703551963838900441754957313651269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17619817150932886549996592140000000000000)
      constant := (423542587071201511164729319820170745394924) }

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
  base := (-7771839407773950351827358999739567548849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2220902878249811470291047442370000000000000)
      constant := (55043341047509087400680202525331805950531995) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel203
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
  base := (-3875955358250999892371987499950207636931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17708183879731377169397532600000000000000)
      constant := (427998444581238399915767402432699169452276) }

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
  base := (-3875955358543345841781353645181762271589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-159431220434172949166826138595000000000000)
      constant := (3972910316377425203097951504115638320494385) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel204
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
  base := (-7731500320428831119892762532936757999129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17796550608529867788798473060000000000000)
      constant := (432477357184417392865244328074126484001742) }

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
  base := (-7731500320939073901738941295458038907277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2243171293907031106380084438290000000000000)
      constant := (56201128910909677364953013060764780467717135) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel205
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
  base := (-1927652059423227209492103748741763303753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17884917337328358408199413520000000000000)
      constant := (436979324843121515703717758972565893569976) }

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
  base := (-3855304119069097354958456937874359682939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1127152750867820462212301468125000000000000)
      constant := (28392247243889261014026434791945781877679945) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel206
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
  base := (-961154310859984382868888081098678044413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-17973284066126849027600353980000000000000)
      constant := (441504347520179484183227350602421151289392) }

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
  base := (-7689234487268484415863637890354785887089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2265439709564250742469121434210000000000000)
      constant := (57370841155337301407267972476515077457663195) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel207
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
  base := (-7667379086356231091742228518219550356183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18061650794925339647001294440000000000000)
      constant := (446052425178858295709970308916060899287634) }

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
  base := (-479211192918461712430038999738982246981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1138286958696430280256819966085000000000000)
      constant := (28980084454543240814834725813890594795917240) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel208
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
  base := (-477815128392059947628916020682565281077/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18150017523723830266402234900000000000000)
      constant := (450623557782855985808504894458157911005536) }

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
  base := (-7645042054568964054637356599591180238353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2287708125221470378558158430130000000000000)
      constant := (58552477744579297898318283357868160841603515) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel209
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
  base := (-952777926071133058215064466508665381727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18238384252522320885803175360000000000000)
      constant := (455217745296294544095214851938361353892368) }

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
  base := (-1524444681765483104999408125378922100819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2298842333050080196602676928090000000000000)
      constant := (59147767657420890933457982460092820426496725) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel210
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
  base := (-949865395871879991849795801599324994883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18326750981320811505204115820000000000000)
      constant := (459834987683712984705935061974410800081872) }

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
  base := (-3799461583600266707350350685952993578947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-164998324348477858189085387575000000000000)
      constant := (4267574188804818699423356981241645224736855) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel211
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
  base := (-7575141347016256189308170008368693729229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18415117710119302124605056280000000000000)
      constant := (464475284910060566400641601295762612541542) }

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
  base := (-3787570673606538299788037254129892095239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1160555374353649916345856962005000000000000)
      constant := (30173645348912722274573766974849176436666445) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel212
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
  base := (-7550877966016278908685920492430496879717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18503484438917792744005996740000000000000)
      constant := (469138636940690157820462481955139006240566) }

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
  base := (-1887719491547019285298479091686111672243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1166122478267954825368116210985000000000000)
      constant := (30475761908425348175017377897997805280600930) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel213
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
  base := (-1881533260275028943672532461466215005267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18591851167716283363406937200000000000000)
      constant := (473825043741351743601880679990770279957864) }

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
  base := (-1881533260312519309960083126075125769341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1171689582182259734390375459965000000000000)
      constant := (30779368998073852177759283707412188373022910) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel214
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
  base := (-468806661824837189272303539984586809949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18680217896514773982807877660000000000000)
      constant := (478534505278186067262824078260493222081632) }

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
  base := (-1875226647332074770109507335686812376847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1177256686096564643412634708945000000000000)
      constant := (31084466615784404565146452866419461935344970) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel215
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
  base := (-7475198627045477587719082696118051436469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18768584625313264602208818120000000000000)
      constant := (483267021517718406967226713120263897127062) }

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
  base := (-3737599313579874677113241410271598220133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1182823790010869552434893957925000000000000)
      constant := (31391054759506722017502049572558458436067415) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel216
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
  base := (-7449009171192504584717313369676596095179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18856951354111755221609758580000000000000)
      constant := (488022592426852480451207573860646807809642) }

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
  base := (-7449009171292260171754844546873905975903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2376781787850348922914306413810000000000000)
      constant := (63398266854427390202567605507407893035903765) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel217
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
  base := (-371116911900019104926826796380392329947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-18945318082910245841010699040000000000000)
      constant := (492801217972864475556396685947284306802120) }

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
  base := (-7422338238087468019875136821053921471671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-341130856525565534422689273110000000000000)
      constant := (9145343604828863813386382765197112748491515) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel218
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
  base := (-3697592921823852393744158982602376371393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19033684811708736460411639500000000000000)
      constant := (497602898123397202966170914189590494514428) }

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
  base := (-7395185843723732356279905018586051232367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2399050203507568559003343409730000000000000)
      constant := (64639524653173715441280647075034417448070085) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel219
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
  base := (-3683776002066310025991832031151699019773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19122051540507227079812579960000000000000)
      constant := (502427632846454367879708249427893203920908) }

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
  base := (-7367552004198995379478008332453046354739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2410184411336178377047861907690000000000000)
      constant := (65264625108622900606660838161091003643088945) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel220
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
  base := (-458714795954727143527688959429211289241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19210418269305717699213520420000000000000)
      constant := (507275422110394957488167793398265238744288) }

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
  base := (-3669718367666792229769376702243426398371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1210659309582394097546190202825000000000000)
      constant := (32946353298136810992089136243650360532399105) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel221
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
  base := (-3655420026361181398886684731729796170481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19298784998104208318614460880000000000000)
      constant := (512146265883927741237735598835580815318076) }

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
  base := (-7310840052772958665296443832056366707037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2432452826993398013136898903610000000000000)
      constant := (66523769112292742101968545672308190156775935) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel222
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
  base := (-3640880985973112315812207720215867152833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19387151726902698938015401340000000000000)
      constant := (517040164136105880977112239659136531388668) }

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
  base := (-5688876540617500606648836529201540619/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1221793517411003915590708700785000000000000)
      constant := (33578906326444653339495298543135198430940800) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel223
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
  base := (-7252202508251084054933725548595238835379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19475518455701189557416341800000000000000)
      constant := (521957116836321648192422587335309522329242) }

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
  base := (-3626101254144828062405984007742559303071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1227360621325308824612967949765000000000000)
      constant := (33897418607156949054497414169802072970747605) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel224
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
  base := (-1444432335354767938724827093021145617221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19563885184499680176817282260000000000000)
      constant := (526897123954301245631820970509788543827790) }

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
  base := (-1444432335361503912925461571657928256003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-352265064354175352467207771070000000000000)
      constant := (9776406113265428807520964118655862555199475) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel225
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
  base := (-1438327898497392567534574811639319444151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19652251913298170796218222720000000000000)
      constant := (531860185460099730715352931446106805558490) }

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
  base := (-22473873414113661983546557358360948191/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1238494829153918642657486447725000000000000)
      constant := (34538914692426692014472829191177250830912800) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel226
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
  base := (-7160635970200986101672025451839925803699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19740618642096661415619163180000000000000)
      constant := (536846301324096038213834301896320148392602) }

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
  base := (-895079496278333316541722233704869665493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1244061933068223551679745696705000000000000)
      constant := (34861898493335742053288896297735227727816860) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel227
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
  base := (-3564575562283471833665825377794546800057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19828985370895152035020103640000000000000)
      constant := (541855471516988099763844959641321812799772) }

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
  base := (-1425830224917873776895639656645391950443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2499258073965056921404009891370000000000000)
      constant := (70372745594722815404914859759327394860707325) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel228
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
  base := (-709718497007876428490247075332166116223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-19917352099693642654421044100000000000000)
      constant := (546887696009788057864883463113356677675540) }

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
  base := (-7097184970098347466303455416336399033331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2510392281793666739448528389330000000000000)
      constant := (71024675205456380123048712397805582236833905) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel229
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
  base := (-883092190134452271616271623495467602713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20005718828492133273821984560000000000000)
      constant := (551942974773817572079858437226572518356592) }

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
  base := (-220773047534147499419735189821183634521/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1260763244811138278746523443645000000000000)
      constant := (35839792907679547211795983096801960152677680) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel230
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
  base := (-7031808791744218920122319930535530711851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20094085557290623893222925020000000000000)
      constant := (557021307780703215231354757038928938576298) }

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
  base := (-878976098969894273423693827407759255663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1266330348725443187768782692625000000000000)
      constant := (36168738710477612352975235878990395929450260) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel231
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
  base := (-6998398796121081459065131926025106733213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20182452286089114512623865480000000000000)
      constant := (562122695002371957454199981860449786533574) }

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
  base := (-6998398796134125017511914137125667622699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-363399272182785170511726269030000000000000)
      constant := (10428335716972262087351043534986601633205535) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel232
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
  base := (-1392901509618947429818644775843245274897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20270819014887605132024805940000000000000)
      constant := (567247136411046736029724881881567547251030) }

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
  base := (-3482253774053064460350142381330325271401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1277464556554053005813301190585000000000000)
      constant := (36831101802754121255065778230678070308506755) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel233
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
  base := (-86626688267598837182261545444175993739/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20359185743686095751425746400000000000000)
      constant := (572394631979242108989180801411431841001760) }

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
  base := (-866266882677232051427472307961411418587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1283031660468357914835560439565000000000000)
      constant := (37164519088847744612964636747606816809784740) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel234
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
  base := (-6895281349659633835251798591631773841767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20447552472484586370826686860000000000000)
      constant := (577565181679759990533120605656736452316466) }

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
  base := (-689528134966832379441456054373021504459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1288598764382662823857819688545000000000000)
      constant := (37499426866017907882094067673559048657037725) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel235
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
  base := (-6859946426307374876603512306868379636877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20535919201283076990227627320000000000000)
      constant := (582758785485685466370548967498763240726246) }

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
  base := (-1714986606578741250419049831746195923193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1294165868296967732880078937525000000000000)
      constant := (37835825132616075405785103888819363997635430) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel236
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
  base := (-6824130304669054781308123259916752105541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20624285930081567609628567780000000000000)
      constant := (587975443370382687136121769980166495788918) }

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
  base := (-6824130304675684453312143865099514441513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2599465944422545283804676373010000000000000)
      constant := (76347427774021607785149165769122618961829315) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel237
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
  base := (-13257486324072423664371067546178471623/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20712652658880058229029508240000000000000)
      constant := (593215155307490838096254302835213245058048) }

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
  base := (-1357566599586174365769962076397528853879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2610600152251155101849194870970000000000000)
      constant := (77026186255174991213440792346711027153998225) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel238
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
  base := (-1350210903824064240793790929086718714967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20801019387678548848430448700000000000000)
      constant := (598477921270920183405314861329132812850330) }

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
  base := (-3375527259562689805690268328914136120307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (338)
      previous := (117)
      next := (0)
      square := (1546417753973585839516458050000000000000)
      linear := (-187266740005697494278122383495000000000000)
      constant := (5550566121821165159863407839590005235789255) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel239
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
  base := (-6713794881166045565546733979234599174539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20889386116477039467831389160000000000000)
      constant := (603763741234848183221692032394030801650922) }

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
  base := (-3356897440585232121768785639085740486057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1316434283954187368969115933445000000000000)
      constant := (39196323060911156515322386044154993580916035) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel240
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
  base := (-6676054096841831753494003035775618738613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-20977752845275530087232329620000000000000)
      constant := (609072615173715682040180459128448762522774) }

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
  base := (-6676054096845691711755115491135209141771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2644002775736984555982750364850000000000000)
      constant := (79080347501021999924435600043071873760266105) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel241
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
  base := (-1327566435759487275413044625220193908283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21066119574074020706633270080000000000000)
      constant := (614404543062223166642271218910298060917170) }

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
  base := (-3318916089400404176682957175319696405351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1327568491782797187013634431405000000000000)
      constant := (39885514919998092533406835540167674380689005) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel242
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
  base := (-3299564569777315947801165396702050974929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21154486302872511326034210540000000000000)
      constant := (619759524875327092109280438653191796100284) }

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
  base := (-6599129139557577660015153108774405718307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2666271191394204192071787360770000000000000)
      constant := (80464693135677036402325914813338270599014785) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel243
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
  base := (-409996561969313146065172277464240206631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21242853031671001945435151000000000000000)
      constant := (625137560588236274385333257553644313387808) }

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
  base := (-81999312393894797879308627482711933113/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1338702699611407005058152929365000000000000)
      constant := (40580668692513817901152537962988423055492600) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel244
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
  base := (-6520279746931754477822504625330728581319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21331219760469492564836091460000000000000)
      constant := (630538650176408347917557666489338542837362) }

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
  base := (-6520279746934002805184714407220216390207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2688539607051423828160824356690000000000000)
      constant := (81860962585041545161247758165423046984399285) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel245
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
  base := (-3240066708985688600412193677270156078989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21419586489267983184237031920000000000000)
      constant := (635962793615546286940188041453419375684044) }

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
  base := (-6480133417973341499211266073771349117959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (676)
      previous := (234)
      next := (0)
      square := (3092835507947171679032916100000000000000)
      linear := (-385667687840004806600763264950000000000000)
      constant := (11794795533248911469294047378368002780871435) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel246
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
  base := (-643950601665542972919052601238993738757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21507953218066473803637972380000000000000)
      constant := (641409990881594989006940139675220125224860) }

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
  base := (-6439506016657145924540709771552874514749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4732)
      previous := (1638)
      next := (0)
      square := (21649848555630201753230412700000000000000)
      linear := (-2710808022708643464249861352610000000000000)
      constant := (83269155825183392400768287054981545743886495) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel247
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
  base := (-399899847180761213464535702757829804369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21596319946864964423038912840000000000000)
      constant := (646880241950737919412790659864249446260192) }

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
  base := (-639839755489367888364627791385279014877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1360971115268626641147189925285000000000000)
      constant := (41988861929723528560885841221692033206775675) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel248
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
  base := (-1589202011118064436900608688674623933779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21684686675663455042439853300000000000000)
      constant := (652373546799393815181635778610603008529768) }

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
  base := (-63568080444735678915725447501066725923/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1366538219182931550169449174265000000000000)
      constant := (42344636416322335353441298561335932607443250) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell002.Kernel249
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
  base := (-1262947499414055843424371818966406183423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20000000000000000000000000000000000000000
      center := (39)
      previous := (13)
      next := (0)
      square := (176733457596981238801880920000000000000)
      linear := (-21773053404461945661840793760000000000000)
      constant := (657889905404213447330632010812835938165770) }

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
  base := (-631473749707142397048721604301887838751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2366)
      previous := (819)
      next := (0)
      square := (10824924277815100876615206350000000000000)
      linear := (-1372105323097236459191708423245000000000000)
      constant := (42701901370957976727834971590491187397530025) }

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
end ForestUnimodality.Stage170KernelData.Cell002.Kernel249
