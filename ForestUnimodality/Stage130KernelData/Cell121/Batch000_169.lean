import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell121.Parameters
import ForestUnimodality.BinomialMassData.Q11_21.Batch000_049
import ForestUnimodality.BinomialMassData.Q11_21.Batch050_099
import ForestUnimodality.BinomialMassData.Q11_21.Batch100_149
import ForestUnimodality.BinomialMassData.Q11_21.Batch150_199
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch000_049
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch050_099
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch100_149
import ForestUnimodality.BinomialMassData.Q1549_2954.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree000.table
  base := (36466604518224870224436529/500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-44739876259645150469168584000000000000)
      constant := (729332090364497404488730580000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree000.table
  base := (36466604518224870224436529/500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-44739876259645150469168584000000000000)
      constant := (729332090364497404488730580000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree001.table
  base := (12638871365561717986461998800401392150331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-349020559864263938687489742744000000000000)
      constant := (178456330313146069985677639546768446025471072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree001.table
  base := (101023822167696768523310323534061960944467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-1728281701238885369523029530588736000000000000)
      constant := (882024313548969791980445817680370688388888600172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49940556791030438457/100000000000000000000)
  directionHi := (24970278395515219229/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree002.table
  base := (239172815976553118329645117245317378267401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-678310834298024366018076139944000000000000)
      constant := (105840852432184392166760390721392963815923841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree002.table
  base := (14926224931369649891511568766057395743847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-3358962064960943313588204189292536000000000000)
      constant := (522804411819081980285095031541057223674860833008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/100000000000000000000)
  centralHi := (24970278395515219229/50000000000000000000)
  directionLo := (70626612726339020493/100000000000000000000)
  directionHi := (35313306363169510247/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree003.table
  base := (152001998078468763172186327805911324752629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-111955678747976088149851393016000000000000)
      constant := (7537785567240089802990790576057654912878821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree003.table
  base := (30344887398457411957827568798826691341051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-4989642428683001257653378847996336000000000000)
      constant := (334992684795080681054741121984877063672758234895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70626612726339020493/100000000000000000000)
  centralHi := (35313306363169510247/50000000000000000000)
  directionLo := (3459983268813746003/4000000000000000000)
  directionHi := (21624895430085912519/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree004.table
  base := (3239444569308871892546525725395450580977/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-1336891383165545220679248934344000000000000)
      constant := (47136264462520755962130635329996598598747424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree004.table
  base := (103459222466736813040309069430821128387083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-6620322792405059201718553506700136000000000000)
      constant := (232744700003552586573236003505515849389144789907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3459983268813746003/4000000000000000000)
  centralHi := (21624895430085912519/25000000000000000000)
  directionLo := (49940556791030438457/50000000000000000000)
  directionHi := (19976222716412175383/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree005.table
  base := (7511077785502535083845610923986971706367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-1666181657599305648009835331544000000000000)
      constant := (35331594864224263142739397204302545225078470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree005.table
  base := (74963309589978651951074495534193793509621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-8251003156127117145783728165403936000000000000)
      constant := (174479106014247132841062874925797582161249990509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/50000000000000000000)
  centralHi := (19976222716412175383/20000000000000000000)
  directionLo := (111670479818932819983/100000000000000000000)
  directionHi := (6979404988683301249/6250000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree006.table
  base := (57009083779421623628257230481719248764829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-221719103559229563926713525416000000000000)
      constant := (3145305809828155834826994385940243189476621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree006.table
  base := (56899362053220239653965323494202064215883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-9881683519849175089848902824107736000000000000)
      constant := (139826232886780882004069395046434030946811025107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111670479818932819983/100000000000000000000)
  centralHi := (6979404988683301249/6250000000000000000)
  directionLo := (1223288816085098469/1000000000000000000)
  directionHi := (122328881608509846901/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree007.table
  base := (8940336807432537230645882766546802360959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-47444126662588295972877716856000000000000)
      constant := (490034263174160196312081820366606106243155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree007.table
  base := (11154264593792666528303373754666150607403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-234946201705535368039062805771664000000000000)
      constant := (2421250396946831762915030763864104764768755852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1223288816085098469/1000000000000000000)
  centralHi := (122328881608509846901/100000000000000000000)
  directionLo := (132130293605164425641/100000000000000000000)
  directionHi := (66065146802582212821/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree008.table
  base := (4475842545031226693991339985408051046501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-2654052480900586930001594523144000000000000)
      constant := (21392984009278166796390681098151604092055528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree008.table
  base := (17869555723701177405000723100230272431273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-13143044247293290977979252141515336000000000000)
      constant := (105738094936727853401844650701781419973445112834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132130293605164425641/100000000000000000000)
  centralHi := (66065146802582212821/50000000000000000000)
  directionLo := (141253225452678040987/100000000000000000000)
  directionHi := (35313306363169510247/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree009.table
  base := (7264899788997687266586902641613471126879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-331482528370483039703575657816000000000000)
      constant := (2210439488367674312717221654060240340868284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree009.table
  base := (29004000257046360946008825140451244793973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-14773724611015348922044426800219136000000000000)
      constant := (98364664672097196784158825905578857604151124717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141253225452678040987/100000000000000000000)
  centralHi := (35313306363169510247/25000000000000000000)
  directionLo := (149821670373091315371/100000000000000000000)
  directionHi := (37455417593272828843/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree010.table
  base := (2969336486841334191558366694207626543231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-3312633029768107784662767317544000000000000)
      constant := (19203437332048780422155150386204506444518968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree010.table
  base := (11854044701333872070589678615933551695953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-16404404974737406866109601458922936000000000000)
      constant := (94985977622845822477415248354101970195441304274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149821670373091315371/100000000000000000000)
  centralHi := (37455417593272828843/25000000000000000000)
  directionLo := (4935184596145181297/3125000000000000000)
  directionHi := (31585181415329160301/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree011.table
  base := (4868502684857366040992580324927109258413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-3641923304201868211993353714744000000000000)
      constant := (19137088363362607470724747509715420731840532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree011.table
  base := (1943449598627561108598462977978601746901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-18035085338459464810174776117626736000000000000)
      constant := (94692591657402554990971709429410036903151916290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4935184596145181297/3125000000000000000)
  centralHi := (31585181415329160301/20000000000000000000)
  directionLo := (165634088697283268179/100000000000000000000)
  directionHi := (8281704434864163409/5000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree012.table
  base := (15953335690532976944263612077640559482717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-441245953181736515480437790216000000000000)
      constant := (2175376385494130272093973437276387414653133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree012.table
  base := (397990884588232617009786163619752246447/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-19665765702181522754239950776330536000000000000)
      constant := (96909489273814144982049890572521971937571098520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165634088697283268179/100000000000000000000)
  centralHi := (8281704434864163409/5000000000000000000)
  directionLo := (172999163440687300151/100000000000000000000)
  directionHi := (21624895430085912519/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree013.table
  base := (6507513395767987526928531169386949254879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-4300503853069389066654526509144000000000000)
      constant := (20448995429483665919123213758551289242803278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree013.table
  base := (649311254533460512615122957063036138143/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-21296446065903580698305125435034336000000000000)
      constant := (101249923548936384014643935457107621268139212940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172999163440687300151/100000000000000000000)
  centralHi := (21624895430085912519/12500000000000000000)
  directionLo := (90031619117640794793/50000000000000000000)
  directionHi := (180063238235281589587/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree014.table
  base := (5266629515079604640422640490306258243471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-94485594438839785591532916456000000000000)
      constant := (442722926797080387328710785769512648382478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree014.table
  base := (5254323383059105985682483179663759755637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-467900539380115074334087757015064000000000000)
      constant := (2192650090360956901397558085010196496161429754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90031619117640794793/50000000000000000000)
  centralHi := (180063238235281589587/100000000000000000000)
  directionLo := (186860453216762562323/100000000000000000000)
  directionHi := (46715113304190640581/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree015.table
  base := (4207642971562145354288975706352038410529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-551009377992989991257299922616000000000000)
      constant := (2585641136651246901839312839062499764231842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree015.table
  base := (4197140717139155121387489365113293643821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-24557806793347696586435474752441936000000000000)
      constant := (115277230928848328985505970355894966739022364618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186860453216762562323/100000000000000000000)
  centralHi := (46715113304190640581/25000000000000000000)
  directionLo := (188885688234361919/97656250000000000)
  directionHi := (193418944751986605057/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree016.table
  base := (6590790511142481564385275775151702956233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-5288374676370670348646285700744000000000000)
      constant := (25150026074390181973716794048905901003698753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree016.table
  base := (1643224684082538072406314479955105996979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-26188487157069754530500649411145736000000000000)
      constant := (124608843487975882621667137292460985721934403564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188885688234361919/97656250000000000)
  centralHi := (193418944751986605057/100000000000000000000)
  directionLo := (49940556791030438457/25000000000000000000)
  directionHi := (199762227164121753829/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree017.table
  base := (2502722592064782333367149846942868087903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-5617664950804430775976872097944000000000000)
      constant := (27307232497056678773539731115771609653530446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree017.table
  base := (998047319836636938503462202908349892997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-27819167520791812474565824069849536000000000000)
      constant := (135316317819022387166496872127956170168599262065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/25000000000000000000)
  centralHi := (199762227164121753829/100000000000000000000)
  directionLo := (102955095325787931057/50000000000000000000)
  directionHi := (41182038130315172423/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree018.table
  base := (3616759072770672693790743648067908069551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-660772802804243467034162055016000000000000)
      constant := (3302627890630317336343745498163327495407999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree018.table
  base := (1801929019340461726211277266019723347573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-29449847884513870418630998728553336000000000000)
      constant := (147307076410377932238078348166710570109415158234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102955095325787931057/50000000000000000000)
  centralHi := (41182038130315172423/20000000000000000000)
  directionLo := (211879838179017061481/100000000000000000000)
  directionHi := (105939919089508530741/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree019.table
  base := (3825980923807830462057131483159425451/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-6276245499671951630638044892344000000000000)
      constant := (32384510732277226715793644048821816639931875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree019.table
  base := (2380315763850304482483741326509387808567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-31080528248235928362696173387257136000000000000)
      constant := (160508153026813340312073961899985252276635358943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211879838179017061481/100000000000000000000)
  centralHi := (105939919089508530741/50000000000000000000)
  directionLo := (27210730029531948539/12500000000000000000)
  directionHi := (217685840236255588313/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree020.table
  base := (260469510349913485718085886106970573997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-6605535774105712057968631289544000000000000)
      constant := (35278109867892212218189751276945870115663385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree020.table
  base := (129311681909051927226080682868334639751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-32711208611957986306761348045960936000000000000)
      constant := (174861752517389735199511909708049071983213592790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27210730029531948539/12500000000000000000)
  centralHi := (217685840236255588313/100000000000000000000)
  directionLo := (111670479818932819983/50000000000000000000)
  directionHi := (223340959637865639967/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree021.table
  base := (328997739782790054948028613943086607441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-15725229135010141690020901784000000000000)
      constant := (87063827301766617677643415637943086607441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree021.table
  base := (40151108191410594298021879509373873951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-700854877054694780629112708258464000000000000)
      constant := (3884121399884566676545234853546408673937379768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111670479818932819983/50000000000000000000)
  centralHi := (223340959637865639967/100000000000000000000)
  directionLo := (228856381743137906619/100000000000000000000)
  directionHi := (11442819087156895331/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree022.table
  base := (-2131290157270986351656938653111616631/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-7264116322973232912629804083944000000000000)
      constant := (41728216324350073167814366776106310928826624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree022.table
  base := (-276086746044105759142388779690996642269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-35972569339402102194891697363368536000000000000)
      constant := (206852167061717511248693882044231711571975101398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228856381743137906619/100000000000000000000)
  centralHi := (11442819087156895331/5000000000000000000)
  directionLo := (11712098731350308441/5000000000000000000)
  directionHi := (234241974627006168821/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree023.table
  base := (-1334878416391063778668953811801163667107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-7593406597406993339960390481144000000000000)
      constant := (45271405079273605239875451801187686822805813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree023.table
  base := (-1340402295261917416863394103940173567159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-37603249703124160138956872022072336000000000000)
      constant := (224423236423202716888113285892920915098209193889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11712098731350308441/5000000000000000000)
  centralHi := (234241974627006168821/100000000000000000000)
  directionLo := (239506496550212888431/100000000000000000000)
  directionHi := (14969156034388305527/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree024.table
  base := (-1024755564547134002380183121388118719071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-880299652426750418587886319816000000000000)
      constant := (5446665937530497062377959988247964365531042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree024.table
  base := (-1027077794900930426813352032005790664547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-39233930066846218083022046680776136000000000000)
      constant := (243011862212197116629537286613009262994722895274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239506496550212888431/100000000000000000000)
  centralHi := (14969156034388305527/6250000000000000000)
  directionLo := (244657763217019693801/100000000000000000000)
  directionHi := (122328881608509846901/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree025.table
  base := (-674516655134781694058390624589859486041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-8251987146274514194621563275544000000000000)
      constant := (52970207232696527690349530385823487866623676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree025.table
  base := (-2701968386395941434216946267302720400831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-40864610430568276027087221339479936000000000000)
      constant := (262599425055369747534168776576929013666695549401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244657763217019693801/100000000000000000000)
  centralHi := (122328881608509846901/50000000000000000000)
  directionLo := (49940556791030438457/20000000000000000000)
  directionHi := (124851391977576096143/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree026.table
  base := (-3287392963277822701966565745354726539683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-8581277420708274621952149672744000000000000)
      constant := (57119026464044255096203915059402565595999797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree026.table
  base := (-102833391708089897092957616916757716731/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-42495290794290333971152395998183736000000000000)
      constant := (283171029800778464443494002924971694559281225632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/20000000000000000000)
  centralHi := (124851391977576096143/50000000000000000000)
  directionLo := (127323936798576436769/50000000000000000000)
  directionHi := (254647873597152873539/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree027.table
  base := (-3822974136466248858566688813715021966599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-990063077238003894364748452216000000000000)
      constant := (6829336966334434103575663217439963923636649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree027.table
  base := (-956430621818586418492561070132275605679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-44125971158012391915217570656887536000000000000)
      constant := (304714751223366693787805223750630709720874787236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127323936798576436769/50000000000000000000)
  centralHi := (254647873597152873539/100000000000000000000)
  directionLo := (129749372580515475113/50000000000000000000)
  directionHi := (259498745161030950227/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree028.table
  base := (-4309205085874972948844315241142843634687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-188568529991342764828843315656000000000000)
      constant := (1347005872663442098802883937517714407287817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree028.table
  base := (-2155755041174055383299515938471636882303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-933809214729274486924137659501864000000000000)
      constant := (6677980297536559382773532991060960508725976274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129749372580515475113/50000000000000000000)
  centralHi := (259498745161030950227/100000000000000000000)
  directionLo := (264260587210328851283/100000000000000000000)
  directionHi := (66065146802582212821/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree029.table
  base := (-2374805324843282353479485445446835881719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-9569148244009555903943908864344000000000000)
      constant := (70735237200902009570920596097931890752323842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree029.table
  base := (-593942899575849707191842838374900376837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-47387331885456507803347919974295136000000000000)
      constant := (350682218607629053370705418351830449646553249816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264260587210328851283/100000000000000000000)
  centralHi := (66065146802582212821/25000000000000000000)
  directionLo := (16808633054984948541/6250000000000000000)
  directionHi := (268938128879759176657/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree030.table
  base := (-41176159813258195201982546342560371583/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1099826502049257370141610584616000000000000)
      constant := (8406514818176493417002569973331817724054125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree030.table
  base := (-2574319952008772714853056761056042440259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-49018012249178565747413094632998936000000000000)
      constant := (375092155598296165675769684963582825582688447978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16808633054984948541/6250000000000000000)
  centralHi := (268938128879759176657/100000000000000000000)
  directionLo := (54707138977630366789/20000000000000000000)
  directionHi := (136767847444075916973/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree031.table
  base := (-5503705595812452196499545927842569334257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-10227728792877076758605081658744000000000000)
      constant := (80772474063267776963654102304445426923592663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree031.table
  base := (-5505063304253137808877218627030041160787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-50648692612900623691478269291702736000000000000)
      constant := (400445908533726678462613541143281327336549496677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54707138977630366789/20000000000000000000)
  centralHi := (136767847444075916973/50000000000000000000)
  directionLo := (278057252360988113437/100000000000000000000)
  directionHi := (139028626180494056719/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree032.table
  base := (-1164298875770082867473015451742845351879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-10557019067310837185935668055944000000000000)
      constant := (86075953649521060740245456484235025999106805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree032.table
  base := (-2911316132552382958186281326805034923463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-52279372976622681635543443950406536000000000000)
      constant := (426739509501086942355525061625895589936905370146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278057252360988113437/100000000000000000000)
  centralHi := (139028626180494056719/50000000000000000000)
  directionLo := (11300258036214243279/4000000000000000000)
  directionHi := (35313306363169510247/12500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree033.table
  base := (-76273201665545229358303195909858519149/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1209589926860510845918472717016000000000000)
      constant := (10174269326361437590434515707281354604935920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree033.table
  base := (-610280981797649905530831771042086083971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-53910053340344739579608618609110336000000000000)
      constant := (453969766854941069451746526587591867873208283410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11300258036214243279/4000000000000000000)
  centralHi := (35313306363169510247/12500000000000000000)
  directionLo := (286886657089064535451/100000000000000000000)
  directionHi := (71721664272266133863/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree034.table
  base := (-3172987189920734528433609026545339588329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-11215599616178358040596840850344000000000000)
      constant := (97249362993768822156176326582923010483093822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree034.table
  base := (-396673360008941409112614917928926832251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-55540733704066797523673793267814136000000000000)
      constant := (482134111196378125498407642933851362825060931536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286886657089064535451/100000000000000000000)
  centralHi := (71721664272266133863/25000000000000000000)
  directionLo := (9100030757821508547/3125000000000000000)
  directionHi := (58240196850057654701/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree035.table
  base := (-6554802932850582485862321031876951653483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-235609997767594254447498515256000000000000)
      constant := (2104456126265379481643015242073107435118653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree035.table
  base := (-1311094616136411903180875246204723689467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-1166763552403854193219162610745264000000000000)
      constant := (10433274944453155837166814161012287483106198465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9100030757821508547/3125000000000000000)
  centralHi := (58240196850057654701/20000000000000000000)
  directionLo := (73863079597038353331/25000000000000000000)
  directionHi := (11818092735526136533/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree036.table
  base := (-3364555579399495417276848496041488994409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1319353351671764321695334849416000000000000)
      constant := (12130560691813154827465353313403934078547918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree036.table
  base := (-42060456782554821381778007960393910959/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-58802094431510913411804142585221736000000000000)
      constant := (541257180564027001681778427011414549091123790240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73863079597038353331/25000000000000000000)
  centralHi := (11818092735526136533/4000000000000000000)
  directionLo := (149821670373091315371/50000000000000000000)
  directionHi := (299643340746182630743/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree037.table
  base := (-429345012698620691916257358147183175467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-12203470439479639322588600041944000000000000)
      constant := (115419177186551583193453647097761475513904848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree037.table
  base := (-858748938294483985039978171878832530093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-60432774795232971355869317243925536000000000000)
      constant := (572212888452192798632886501438128980795669982424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149821670373091315371/50000000000000000000)
  centralHi := (299643340746182630743/100000000000000000000)
  directionLo := (6075530951814204969/2000000000000000000)
  directionHi := (303776547590710248451/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree038.table
  base := (-3488266003359971026366239659843614287943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-12532760713913399749919186439144000000000000)
      constant := (121850521711840114202683203524769932198034274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree038.table
  base := (-109014490939088778821455615465247838033/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-62063455158955029299934491902629336000000000000)
      constant := (604096507193982116348665298260553062345197282752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6075530951814204969/2000000000000000000)
  centralHi := (303776547590710248451/100000000000000000000)
  directionLo := (12314170703947817851/4000000000000000000)
  directionHi := (76963566899673861569/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree039.table
  base := (-3525276281235676296407274116997487358429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1429116776483017797472196981816000000000000)
      constant := (14274322306583395052085060898518246238873958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree039.table
  base := (-7050884417260038503947603635115989815533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-63694135522677087243999666561333136000000000000)
      constant := (636907156344330435397626347516187923853710110043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12314170703947817851/4000000000000000000)
  centralHi := (76963566899673861569/25000000000000000000)
  directionLo := (62375735439777324149/20000000000000000000)
  directionHi := (155939338599443310373/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree040.table
  base := (-1772977642515452269503971460959528152147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-13191341262780920604580359233544000000000000)
      constant := (135274169372246232934985364219027392339612692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree040.table
  base := (-283687567390888215290174275758546515751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-65324815886399145188064841220036936000000000000)
      constant := (670644123226201468105933328535344984451005918025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62375735439777324149/20000000000000000000)
  centralHi := (155939338599443310373/50000000000000000000)
  directionLo := (315851814153291603009/100000000000000000000)
  directionHi := (31585181415329160301/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree041.table
  base := (-355043620457516686955793032568603832049/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-13520631537214681031910945630744000000000000)
      constant := (142266210077397517797568950412408914201327820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree041.table
  base := (-284044256685753130728809056390027601821/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-66955496250121203132130015878740736000000000000)
      constant := (705306830400855007521750838239067692895675892275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315851814153291603009/100000000000000000000)
  centralHi := (31585181415329160301/10000000000000000000)
  directionLo := (159887794809769324549/50000000000000000000)
  directionHi := (319775589619538649099/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree042.table
  base := (-3538827083750639408943820894593223303547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-31405718393760638229572634984000000000000)
      constant := (338877386802721838362572197458813553392906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree042.table
  base := (-1769462697997895021934688828194515829153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-1399717890078433899514187561988664000000000000)
      constant := (15120302235568257770892393089303135843081117148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159887794809769324549/50000000000000000000)
  centralHi := (319775589619538649099/100000000000000000000)
  directionLo := (80912949724195002723/25000000000000000000)
  directionHi := (323651798896780010893/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree043.table
  base := (-351121565533095671669808464176323547359/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-14179212086082201886572118425144000000000000)
      constant := (156810244499748326014453891668236826312293620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree043.table
  base := (-7022596595338031117910301602232605778201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-70216856977565319020260365196148336000000000000)
      constant := (777407680442157806147830131060094843749286950671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80912949724195002723/25000000000000000000)
  centralHi := (323651798896780010893/100000000000000000000)
  directionLo := (81870532756648723881/25000000000000000000)
  directionHi := (13099285241063795821/4000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree044.table
  base := (-693534646196385404521467329317859555441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-14508502360515962313902704822344000000000000)
      constant := (164362097939752260828575813679084239360505190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree044.table
  base := (-1387097092839528717828307789052586934543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-71847537341287376964325539854852136000000000000)
      constant := (814845134113540010869022606893370199386366718765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81870532756648723881/25000000000000000000)
  centralHi := (13099285241063795821/4000000000000000000)
  directionLo := (331268177394566536359/100000000000000000000)
  directionHi := (8281704434864163409/2500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree045.table
  base := (-6816515667354828159469935411332452942357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1648643626105524749025921246616000000000000)
      constant := (19122270747083243036673132714364709805824507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree045.table
  base := (-6816632619927448804000952407001208094637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-73478217705009434908390714513555936000000000000)
      constant := (853206919198259461796843764220027031506514640027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331268177394566536359/100000000000000000000)
  centralHi := (8281704434864163409/2500000000000000000)
  directionLo := (335011439456798459949/100000000000000000000)
  directionHi := (6700228789135969199/2000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree046.table
  base := (-3333016722232697106489566107089007458657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-15167082909383483168563877616744000000000000)
      constant := (180025219169464029248264659048731495421464526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree046.table
  base := (-208316621589049311220686940006795097557/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-75108898068731492852455889172259736000000000000)
      constant := (892492831007110408384163942847924857523890411104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335011439456798459949/100000000000000000000)
  centralHi := (6700228789135969199/2000000000000000000)
  directionLo := (169356667848887984413/50000000000000000000)
  directionHi := (338713335697775968827/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree047.table
  base := (-6483976855420436225190176744226703219289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-15496373183817243595894464013944000000000000)
      constant := (188136411292499712730618677885684023880293551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree047.table
  base := (-1621014940720228957397394585306626685887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-76739578432453550796521063830963536000000000000)
      constant := (932702702683847074904084170847571881970254475108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169356667848887984413/50000000000000000000)
  centralHi := (338713335697775968827/100000000000000000000)
  directionLo := (68475041582203486209/20000000000000000000)
  directionHi := (171187603955508715523/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree048.table
  base := (-3135204397557058053654486160708201821233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1758407050916778224802783379016000000000000)
      constant := (21825998372911990263808716397338596221519166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree048.table
  base := (-6270478649223813064561956136665245849539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-78370258796175608740586238489667336000000000000)
      constant := (973836398072258550547689651944646370887101034869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68475041582203486209/20000000000000000000)
  centralHi := (171187603955508715523/50000000000000000000)
  directionLo := (172999163440687300151/50000000000000000000)
  directionHi := (345998326881374600303/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree049.table
  base := (-6025380648513433446126593721205714400337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-329692933320097233684808914456000000000000)
      constant := (4181998340812615946152430696813148570396967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree049.table
  base := (-1506359883028797269444627055160473671961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-1632672227753013605809212513232064000000000000)
      constant := (20732526652104418586594163482932068206602497276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172999163440687300151/50000000000000000000)
  centralHi := (345998326881374600303/100000000000000000000)
  directionLo := (349583897537213069199/100000000000000000000)
  directionHi := (873959743843032673/250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree050.table
  base := (-1149786888015861625852959552767070632261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-16484244007118524877886223205544000000000000)
      constant := (213588192790543254021749452831348609255864495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree050.table
  base := (-5748984099239868555646383578174830566789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-81631619523619724628716587807074936000000000000)
      constant := (1058874835383527567577044145686508640048463359619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349583897537213069199/100000000000000000000)
  centralHi := (873959743843032673/250000000000000000)
  directionLo := (353133063631695102469/100000000000000000000)
  directionHi := (35313306363169510247/10000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree051.table
  base := (-5441104574036345010653078787248508508283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1868170475728031700579645511416000000000000)
      constant := (24716088050680008846059620737280823083094133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree051.table
  base := (-2720573236564875207527571272580909682549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-83262299887341782572781762465778736000000000000)
      constant := (1102779411924198830137216891343147547362277125158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353133063631695102469/100000000000000000000)
  centralHi := (35313306363169510247/10000000000000000000)
  directionLo := (89161728001180864941/25000000000000000000)
  directionHi := (71329382400944691953/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree052.table
  base := (-1275479811185786161553396021397626371319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-17142824555986045732547395999944000000000000)
      constant := (231487705262836515294668838599662587080993284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree052.table
  base := (-510195461245446523904005919625923148977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-84892980251063840516846937124482536000000000000)
      constant := (1147607474582481697887453889216777026987353541670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89161728001180864941/25000000000000000000)
  centralHi := (71329382400944691953/20000000000000000000)
  directionLo := (90031619117640794793/25000000000000000000)
  directionHi := (360126476470563179173/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree053.table
  base := (-4731401580827399391266661695978564117883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-17472114830419806159877982397144000000000000)
      constant := (240716921010967748733449935239385453224013597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree053.table
  base := (-946286289715170180834035311920462966061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-86523660614785898460912111783186336000000000000)
      constant := (1193358973332945312006721351439272219730559563655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90031619117640794793/25000000000000000000)
  centralHi := (360126476470563179173/100000000000000000000)
  directionLo := (363572741370556040159/100000000000000000000)
  directionHi := (2272329633565975251/625000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree054.table
  base := (-2164785287134235489716416238516361176769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-1977933900539285176356507643816000000000000)
      constant := (27792492369450097934039247428449396604676638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree054.table
  base := (-1082398952075838973711485255351735901209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-88154340978507956404977286441890136000000000000)
      constant := (1240033867104358883152293656606157995724685725756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363572741370556040159/100000000000000000000)
  centralHi := (2272329633565975251/625000000000000000)
  directionLo := (183493322412764770351/50000000000000000000)
  directionHi := (366986644825529540703/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree055.table
  base := (-3896441835609011810414901381655547713221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-18130695379287327014539155191544000000000000)
      constant := (259734229320836603605109776465409903458469539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree055.table
  base := (-243528947739106798018163307023673727577/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-89785021342230014349042461100593936000000000000)
      constant := (1287632122143694006503460102831450363228042796272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183493322412764770351/50000000000000000000)
  centralHi := (366986644825529540703/100000000000000000000)
  directionLo := (370369081718354973779/100000000000000000000)
  directionHi := (18518454085917748689/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree056.table
  base := (-429003526057242593779804505059005008547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-376734401096348723303464114056000000000000)
      constant := (5500455292536599634893924668211751639384616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree056.table
  base := (-3432046242808276062699674879110227029231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-1865626565427593312104237464475464000000000000)
      constant := (27268443075207746584928931368420637582431606649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370369081718354973779/100000000000000000000)
  centralHi := (18518454085917748689/5000000000000000000)
  directionLo := (186860453216762562323/50000000000000000000)
  directionHi := (373720906433525124647/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree057.table
  base := (-587268054002462800595666497288682648317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2087697325350538652133369776216000000000000)
      constant := (31055185188986368348270421615156272751162335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree057.table
  base := (-2936355525238909051789918442865787311579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-93046382069674130237172810418001536000000000000)
      constant := (1385598609866418194425166140779048003871958375709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186860453216762562323/50000000000000000000)
  centralHi := (373720906433525124647/100000000000000000000)
  directionLo := (377042935377516094027/100000000000000000000)
  directionHi := (94260733844379023507/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree058.table
  base := (-120469336957920067812101509711753497299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-19118566202588608296530914383144000000000000)
      constant := (289657297575559557702669353039174334153822820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree058.table
  base := (-60234991211538956341242797979515023839/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-94677062433396188181237985076705336000000000000)
      constant := (1435966800844793530764630813967739590782381206760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377042935377516094027/100000000000000000000)
  centralHi := (94260733844379023507/25000000000000000000)
  directionLo := (380335949300998779239/100000000000000000000)
  directionHi := (9508398732524969481/2500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree059.table
  base := (-231396851194961142818847089883704075361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-19447856477022368723861500780344000000000000)
      constant := (300004198785934512341867114078826292022126392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree059.table
  base := (-1851185737704271678849409240322066586349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-96307742797118246125303159735409136000000000000)
      constant := (1487258268076413973331460122975180636401948652379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380335949300998779239/100000000000000000000)
  centralHi := (9508398732524969481/2500000000000000000)
  directionLo := (383600695441614196033/100000000000000000000)
  directionHi := (191800347720807098017/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree060.table
  base := (-31542760544992011678131851660938656159/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2197460750161792127910231908616000000000000)
      constant := (34504151968022761575847194230104560233928360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree060.table
  base := (-15771495951063218718088674234932669059/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-97938423160840304069368334394112936000000000000)
      constant := (1539472998727086976880435426890790285552031103120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383600695441614196033/100000000000000000000)
  centralHi := (191800347720807098017/50000000000000000000)
  directionLo := (386837889503973210113/100000000000000000000)
  directionHi := (193418944751986605057/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree061.table
  base := (-20031202686217856592060862185135352811/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-20106437025889889578522673574744000000000000)
      constant := (321256802189025040353229887434587369901131168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree061.table
  base := (-641006325404699597764004137353912630779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-99569103524562362013433509052816736000000000000)
      constant := (1592610982190653139136451183433871482332489318909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386837889503973210113/100000000000000000000)
  centralHi := (193418944751986605057/50000000000000000000)
  directionLo := (195024108745871675067/50000000000000000000)
  directionHi := (78009643498348670027/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree062.table
  base := (1095693615975402616561993655979132981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-20435727300323650005853259971944000000000000)
      constant := (332162500425140087209761214166470867976446210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree062.table
  base := (136878663981407281525054861082792417/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-101199783888284419957498683711520536000000000000)
      constant := (1646672209694708146360819457573196838644693247440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195024108745871675067/50000000000000000000)
  centralHi := (78009643498348670027/20000000000000000000)
  directionLo := (393232337405107693883/100000000000000000000)
  directionHi := (98308084351276923471/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree063.table
  base := (694152481691535527454372754129380602921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-47086207652511134769124368184000000000000)
      constant := (778354786706409404200747729426129380602921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree063.table
  base := (173536712688441305386883262304722614701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-2098580903102173018399262415718864000000000000)
      constant := (34727687224031208061378457372338316222116412884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393232337405107693883/100000000000000000000)
  centralHi := (98308084351276923471/25000000000000000000)
  directionLo := (15855635232619731077/4000000000000000000)
  directionHi := (198195440407746638463/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree064.table
  base := (28171707283917487271121031995782053943/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-21094307849191170860514432766344000000000000)
      constant := (354532682497364160541885852630962994289443150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree064.table
  base := (35214514744631722071918820049684358571/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-104461144615728535845629033028928136000000000000)
      constant := (1757564369023079316663147626754599738762761402360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15855635232619731077/4000000000000000000)
  centralHi := (198195440407746638463/50000000000000000000)
  directionLo := (49940556791030438457/12500000000000000000)
  directionHi := (399524454328243507657/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree065.table
  base := (2154253273050995710376424567923998651803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-21423598123624931287845019163544000000000000)
      constant := (365997164085668724380403969758214483405445123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree065.table
  base := (1077124611888451440880852418714230440833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-106091824979450593789694207687631936000000000000)
      constant := (1814395289843431807406351574268958762838719947314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/12500000000000000000)
  centralHi := (399524454328243507657/100000000000000000000)
  directionLo := (402633640942828905223/100000000000000000000)
  directionHi := (50329205117853613153/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree066.table
  base := (2931154290756727034932776291647575668579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2416987599784299079463956173416000000000000)
      constant := (41960878317424740297893191397986731207760371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree066.table
  base := (1465575427801652254667550878513370959909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-107722505343172651733759382346335736000000000000)
      constant := (1872149432299952671852243709176458647273598641722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402633640942828905223/100000000000000000000)
  centralHi := (50329205117853613153/12500000000000000000)
  directionLo := (50714875164904312407/12500000000000000000)
  directionHi := (405719001319234499257/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree067.table
  base := (233705426555752253900146292994260944611/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-22082178672492452142506191957944000000000000)
      constant := (389484904108568300210593271259335505225175216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree067.table
  base := (467410488752122506734457693154844365673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-109353185706894709677824557005039536000000000000)
      constant := (1930826792956193820291386414843012877793618032136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50714875164904312407/12500000000000000000)
  centralHi := (405719001319234499257/100000000000000000000)
  directionLo := (408781074958314504641/100000000000000000000)
  directionHi := (204390537479157252321/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree068.table
  base := (4578649552076739849719662582505060222869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-22411468946926212569836778355144000000000000)
      constant := (401508161257294976291175750058756731558285229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree068.table
  base := (4578647078120549641380448561789038402973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-110983866070616767621889731663743336000000000000)
      constant := (1990427368956757660504625941084226967158199285717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408781074958314504641/100000000000000000000)
  centralHi := (204390537479157252321/50000000000000000000)
  directionLo := (102955095325787931057/25000000000000000000)
  directionHi := (411820381303151724229/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree069.table
  base := (2724620685888115181940066124545559023233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2526751024595552555240818305816000000000000)
      constant := (45968630646407436531136791787869464784276834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree069.table
  base := (5449239271599298565972749214059166789063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-112614546434338825565954906322447136000000000000)
      constant := (2050951157927454081234365766773109634066177817327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102955095325787931057/25000000000000000000)
  centralHi := (411820381303151724229/100000000000000000000)
  directionLo := (414837420767788756969/100000000000000000000)
  directionHi := (41483742076778875697/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree070.table
  base := (6351061368185241561099164569694011974469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-470817336648851702540774513256000000000000)
      constant := (8696192803792123170458171373847246107770221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree070.table
  base := (6351059584963663728005639940147753729093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-2331535240776752724694287366962264000000000000)
      constant := (43110166487610843701661147722420198143772949453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414837420767788756969/100000000000000000000)
  centralHi := (41483742076778875697/10000000000000000000)
  directionLo := (417832675699100334407/100000000000000000000)
  directionHi := (52229084462387541801/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree071.table
  base := (7284108778749386755910498320865778435317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-23399339770227493851828537546744000000000000)
      constant := (438695475625449811479542942542285808289974797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree071.table
  base := (7284107264371721459216193637938102977153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-115875907161782941454085255639854736000000000000)
      constant := (2174768367208661423047615400862513657849645606937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417832675699100334407/100000000000000000000)
  centralHi := (52229084462387541801/12500000000000000000)
  directionLo := (420806611277042185649/100000000000000000000)
  directionHi := (8416132225540843713/2000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree072.table
  base := (4124191484072826809601738974745186140691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2636514449406806031017680438216000000000000)
      constant := (50162640028488534302707884740357028241787718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree072.table
  base := (8248381681862316111175983052302080974019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-117506587525504999398150430298558536000000000000)
      constant := (2238061784504728854312462835683429058405170695051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420806611277042185649/100000000000000000000)
  centralHi := (8416132225540843713/2000000000000000000)
  directionLo := (423759676358034122963/100000000000000000000)
  directionHi := (105939919089508530741/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree073.table
  base := (462194170337836113567758448128187046501/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-24057920319095014706489710341144000000000000)
      constant := (464418301045093789020020743569882609750138820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree073.table
  base := (2310970578510394517256537817014598472863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-119137267889227057342215604957262336000000000000)
      constant := (2302278408639334730188905115594017377967625390108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423759676358034122963/100000000000000000000)
  centralHi := (105939919089508530741/25000000000000000000)
  directionLo := (106673076066451732977/25000000000000000000)
  directionHi := (426692304265806931909/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree074.table
  base := (513530482642405714044665546743636284929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-24387210593528775133820296738344000000000000)
      constant := (477559097796735847378213018414774872033073780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree074.table
  base := (1027060872443841660318374677859985903411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-120767948252949115286280779615966136000000000000)
      constant := (2367418238660304708588725873977021355878822954190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106673076066451732977/25000000000000000000)
  centralHi := (426692304265806931909/100000000000000000000)
  directionLo := (429604913533658384419/100000000000000000000)
  directionHi := (21480245676682919221/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree075.table
  base := (5664280668899623992407808222636849515419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2746277874218059506794542570616000000000000)
      constant := (54542905594306811920618197605018411252511062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree075.table
  base := (11328560548885553819396273277805273513727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-122398628616671173230345954274669936000000000000)
      constant := (2433481273773197311934554356818244710523127348583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429604913533658384419/100000000000000000000)
  centralHi := (21480245676682919221/5000000000000000000)
  directionLo := (216248954300859125189/50000000000000000000)
  directionHi := (432497908601718250379/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree076.table
  base := (496709526154219818640185441828403870117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-25045791142396295988481469532744000000000000)
      constant := (504399458565450377830624228454462152668039925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree076.table
  base := (6208868741698890513545338677768450878893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-124029308980393231174411128933373736000000000000)
      constant := (2500467513314859991896853421484923077754761134794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216248954300859125189/50000000000000000000)
  centralHi := (432497908601718250379/100000000000000000000)
  directionLo := (27210730029531948539/6250000000000000000)
  directionHi := (3482973443780089413/800000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree077.table
  base := (1692267480495397744629548343517447358189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-517858804425103192159429712856000000000000)
      constant := (10573449435376375274305314121325256209789608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree077.table
  base := (6769069637056605307229908474524720172723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-2564489578451332430989312318205664000000000000)
      constant := (52415856259826238339912756023674648133619601366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27210730029531948539/6250000000000000000)
  centralHi := (3482973443780089413/800000000000000000)
  directionLo := (10955665183195647313/2500000000000000000)
  directionHi := (438226607327825892521/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree078.table
  base := (14689766193327083374653666183465562371963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2856041299029312982571404703016000000000000)
      constant := (59109426839779182810650649185757812556226187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree078.table
  base := (1468976570894028347101590487497797800027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-127290669707837347062541478250781336000000000000)
      constant := (2637209603560390485356425915957309881368951012830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10955665183195647313/2500000000000000000)
  centralHi := (438226607327825892521/100000000000000000000)
  directionLo := (55132881888705752581/12500000000000000000)
  directionHi := (441063055109646020649/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree079.table
  base := (15872617022393557158304813526897640135097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-26033661965697577270473228724344000000000000)
      constant := (546056916159977992026107298211377859299577777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree079.table
  base := (15872616610616347976334321134102651933817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-128921350071559405006606652909485136000000000000)
      constant := (2706965453414870796872102733034401338170527866193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132881888705752581/12500000000000000000)
  centralHi := (441063055109646020649/100000000000000000000)
  directionLo := (443881378067668861661/100000000000000000000)
  directionHi := (221940689033834430831/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree080.table
  base := (17086692181014576428697796277589946664179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-26362952240131337697803815121544000000000000)
      constant := (560315246073123148777946972230737166478902939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree080.table
  base := (17086691830935324817899474252900698946567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-130552030435281462950671827568188936000000000000)
      constant := (2777644505971610753206202670639689488872205360943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443881378067668861661/100000000000000000000)
  centralHi := (221940689033834430831/50000000000000000000)
  directionLo := (111670479818932819983/25000000000000000000)
  directionHi := (446681919275731279933/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree081.table
  base := (4582997885897682671093412669229203872537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-2965804723840566458348266835416000000000000)
      constant := (63862203471339863946692384634704923959017252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree081.table
  base := (18331991245944400783499446572420400927879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-132182710799003520894737002226892736000000000000)
      constant := (2849246760960203697704702276254559050815794946991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111670479818932819983/25000000000000000000)
  centralHi := (446681919275731279933/100000000000000000000)
  directionLo := (449465011119273946113/100000000000000000000)
  directionHi := (224732505559636973057/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree082.table
  base := (4902128751256604131086906911311117306331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-27021532788998858552464987915944000000000000)
      constant := (589390671620437711153126492312080810928367884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree082.table
  base := (19608514751944550767772351500446691267147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-133813391162725578838802176885596536000000000000)
      constant := (2921772218154427199828526538783381681953327927763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449465011119273946113/100000000000000000000)
  centralHi := (224732505559636973057/50000000000000000000)
  directionLo := (452230975755804666953/100000000000000000000)
  directionHi := (226115487877902333477/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree083.table
  base := (20916262477359358980974869377279288972959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-27350823063432618979795574313144000000000000)
      constant := (604207767169468592415900681737812166437074919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree083.table
  base := (20916262262158350218704320432335634665523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-135444071526447636782867351544300336000000000000)
      constant := (2995220877364973791372145195462937102756243724667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452230975755804666953/100000000000000000000)
  centralHi := (226115487877902333477/50000000000000000000)
  directionLo := (227490062775083279519/50000000000000000000)
  directionHi := (454980125550166559039/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree084.table
  base := (22255233886950409465917740995109282599567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-62766696911261631308676101384000000000000)
      constant := (1404106843212418491567113680291109282599567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree084.table
  base := (22255233703952133254436885080570291192843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-2797443916125912137284337269449064000000000000)
      constant := (62644749763946755588530069874049525934196563203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227490062775083279519/50000000000000000000)
  centralHi := (454980125550166559039/100000000000000000000)
  directionLo := (457712763486275813239/100000000000000000000)
  directionHi := (11442819087156895331/2500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree085.table
  base := (23625429172139182246243327759850443595603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-28009403612300139834456747107544000000000000)
      constant := (634400723654869368140492430723934045625660923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree085.table
  base := (369147328383109217544420063103187444827/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-138705432253891752670997700861707936000000000000)
      constant := (3144887801227026859765057209583788347812864030912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457712763486275813239/100000000000000000000)
  centralHi := (11442819087156895331/2500000000000000000)
  directionLo := (460429183556865341533/100000000000000000000)
  directionHi := (230214591778432670767/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree086.table
  base := (12513424140643635061801339741399338136601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-28338693886733900261787333504744000000000000)
      constant := (649776584541274494919614687851258216236482082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree086.table
  base := (12513424074472563061925373248002658433973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-140336112617613810615062875520411736000000000000)
      constant := (3221106065634811380824061518930512158901613369434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460429183556865341533/100000000000000000000)
  centralHi := (230214591778432670767/50000000000000000000)
  directionLo := (463129671132653445587/100000000000000000000)
  directionHi := (115782417783163361397/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree087.table
  base := (1322974558557206800697525299484327796187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3185331573463073409901991100216000000000000)
      constant := (73926522277424272029377770158166641240263260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree087.table
  base := (6614872764648835297666746566166219269121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-141966792981335868559128050179115536000000000000)
      constant := (3298247531563734660339557024738138146623785064036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463129671132653445587/100000000000000000000)
  centralHi := (115782417783163361397/25000000000000000000)
  directionLo := (58226812914031210347/12500000000000000000)
  directionHi := (465814503312249682777/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree088.table
  base := (13961678902740906362472865167869145448067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-28997274435601421116448506299144000000000000)
      constant := (681087071505524694643025746508012586285195094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree088.table
  base := (349041971372053866783248480518070060297/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-143597473345057926503193224837819336000000000000)
      constant := (3376312198935904494666647980810450596845572329040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58226812914031210347/12500000000000000000)
  centralHi := (465814503312249682777/100000000000000000000)
  directionLo := (468483949254012337641/100000000000000000000)
  directionHi := (234241974627006168821/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree089.table
  base := (5883689630790733893997564361934564283539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-29326564710035181543779092696344000000000000)
      constant := (697021697554010369878601299061121714245203495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree089.table
  base := (29418448072549389922973363196714336167699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-145228153708779984447258399496523136000000000000)
      constant := (3455300067686087406035823843803369703065584231771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468483949254012337641/100000000000000000000)
  centralHi := (234241974627006168821/50000000000000000000)
  directionLo := (94227654098196489819/20000000000000000000)
  directionHi := (58892283811372806137/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree090.table
  base := (773619054778501432126817032909330032089/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3295094998274326885678853232616000000000000)
      constant := (79238064292340600975333420153542286862894440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree090.table
  base := (15472381060954085747234853931501367497917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-146858834072502042391323574155226936000000000000)
      constant := (3535211137759652647667036972908565933472726750186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94227654098196489819/20000000000000000000)
  centralHi := (58892283811372806137/12500000000000000000)
  directionLo := (236888860614968702257/50000000000000000000)
  directionHi := (94755544245987480903/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree091.table
  base := (6500459979149980532884509543948482777831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-611941739977606171396740112056000000000000)
      constant := (14886728871985723427044412261413681725002395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree091.table
  base := (32502299836870150321099367232113492127479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-3030398253800491843579362220692464000000000000)
      constant := (73796845083894948112560957955460118783007492559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236888860614968702257/50000000000000000000)
  centralHi := (94755544245987480903/20000000000000000000)
  directionLo := (238201274317765991493/50000000000000000000)
  directionHi := (476402548635531982987/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree092.table
  base := (34091061249952506069018677630054713405099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-30314435533336462825770851887944000000000000)
      constant := (745943105834852148823420291508422128611648659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree092.table
  base := (34091061199877079253730379659090383080037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-150120194799946158279453923472634536000000000000)
      constant := (3697802881701383010236175045374949656310210036573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238201274317765991493/50000000000000000000)
  centralHi := (476402548635531982987/100000000000000000000)
  directionLo := (479012993100425776863/100000000000000000000)
  directionHi := (14969156034388305527/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree093.table
  base := (17855523119409052865453188098202791781671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3404858423085580361455715365016000000000000)
      constant := (84735861327459609614785003672231873594603758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree093.table
  base := (35711046196230783210616678705727666305599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-151750875163668216223519098131338336000000000000)
      constant := (3780483555499179810641194875009904908147987080871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479012993100425776863/100000000000000000000)
  centralHi := (14969156034388305527/3125000000000000000)
  directionLo := (240804644251116287183/50000000000000000000)
  directionHi := (481609288502232574367/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree094.table
  base := (18681127424924670276446151378848504049819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-30973016082203983680432024682344000000000000)
      constant := (779488653058642124810248162202720380571940358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree094.table
  base := (37362254813630774134265367685492465878077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-153381555527390274167584272790042136000000000000)
      constant := (3864087430477408987318972007306736197594535439733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240804644251116287183/50000000000000000000)
  centralHi := (481609288502232574367/100000000000000000000)
  directionLo := (242095831224034517553/50000000000000000000)
  directionHi := (484191662448069035107/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree095.table
  base := (9761171768147178748095878305382166881509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-31302306356637744107762611079544000000000000)
      constant := (796540809164757308120686190621574142378981876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree095.table
  base := (9761171760446734126784056398493035044343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-155012235891112332111649447448745936000000000000)
      constant := (3948614506613622354854642441477908218989002161788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242095831224034517553/50000000000000000000)
  centralHi := (484191662448069035107/100000000000000000000)
  directionLo := (60845042063428296927/12500000000000000000)
  directionHi := (486760336507426375417/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree096.table
  base := (10189585724572409383574074782758264012321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3514621847896833837232577497416000000000000)
      constant := (90419913362402754400691911430796619746414916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree096.table
  base := (40758342872094997200813816126344094995091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-156642916254834390055714622107449736000000000000)
      constant := (4034064783889049441894647179176797643210545874139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60845042063428296927/12500000000000000000)
  centralHi := (486760336507426375417/100000000000000000000)
  directionLo := (489315526434039387603/100000000000000000000)
  directionHi := (122328881608509846901/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree097.table
  base := (42503222319640658410351888606504674746641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-31960886905505264962423783873944000000000000)
      constant := (831203886346020219919060260570556561563268681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree097.table
  base := (42503222297364525546727753889403160683439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-158273596618556447999779796766153536000000000000)
      constant := (4120438262288004115413010536126950989722581998231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489315526434039387603/100000000000000000000)
  centralHi := (122328881608509846901/25000000000000000000)
  directionLo := (245928721188690786847/50000000000000000000)
  directionHi := (98371488475476314739/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree098.table
  base := (221396626652671211841255781091013591761/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-658983207753857661015395311656000000000000)
      constant := (17322751171739799510467784681371824465169800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree098.table
  base := (11069831327897725289133120809775898610133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-3263352591475071549874387171935864000000000000)
      constant := (85872141669334431059154396340199363128086925172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245928721188690786847/50000000000000000000)
  centralHi := (98371488475476314739/20000000000000000000)
  directionLo := (494386289084373143457/100000000000000000000)
  directionHi := (247193144542186571729/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree099.table
  base := (23043325962936418500205431277429884314123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3624385272708087313009439629816000000000000)
      constant := (96290220385229626364007395638532128662784054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree099.table
  base := (11521662977441024026753133797339740547897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-161534957346000563887910146083561136000000000000)
      constant := (4295954822406268940146007513963502901430852778052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494386289084373143457/100000000000000000000)
  centralHi := (247193144542186571729/50000000000000000000)
  directionLo := (248451133045924902269/50000000000000000000)
  directionHi := (496902266091849804539/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree100.table
  base := (47925202101406184760135833285528632932283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-32948757728806546244415543065544000000000000)
      constant := (884595414499595240130403022769318127123136803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree100.table
  base := (23962601043854146266115321551422431217009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-163165637709722621831975320742264936000000000000)
      constant := (4385097904105539902382076556658097649900820853522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248451133045924902269/50000000000000000000)
  centralHi := (496902266091849804539/100000000000000000000)
  directionLo := (49940556791030438457/10000000000000000000)
  directionHi := (499405567910304384571/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree101.table
  base := (49794975853594817344566617160457461942273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-33278048003240306671746129462744000000000000)
      constant := (902765100511275079054369817453665740716542393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree101.table
  base := (24897487920973668036064746795981196778419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-164796318073444679776040495400968736000000000000)
      constant := (4475164186887616677061831077936417794453655245302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49940556791030438457/10000000000000000000)
  centralHi := (499405567910304384571/100000000000000000000)
  directionLo := (501896384199380122323/100000000000000000000)
  directionHi := (125474096049845030581/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree102.table
  base := (25847986589747748880810190895873975437417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3734148697519340788786301762216000000000000)
      constant := (102346782388978687392717601746307649592866866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree102.table
  base := (25847986584795921421533556510167050141953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-166426998437166737720105670059672536000000000000)
      constant := (4566153670746195989450973486693470461458249172274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501896384199380122323/100000000000000000000)
  centralHi := (125474096049845030581/25000000000000000000)
  directionLo := (252187449967781860949/50000000000000000000)
  directionHi := (504374899935563721899/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree103.table
  base := (2681409703833253280401800845037867355067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-33936628552107827526407302257144000000000000)
      constant := (939663237467117128832830667925745990071690940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree103.table
  base := (53628194068244459837005911276056858090043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-168057678800888795664170844718376336000000000000)
      constant := (4658066355676047944439232547010025739572313415747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252187449967781860949/50000000000000000000)
  centralHi := (504374899935563721899/100000000000000000000)
  directionLo := (253420647786248888063/50000000000000000000)
  directionHi := (506841295572497776127/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree104.table
  base := (27795819271539858836059138341022417621871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-34265918826541587953737888654344000000000000)
      constant := (958391688409309408733128970680397772342490222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree104.table
  base := (27795819267960174249812227837107739032443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-169688359164610853608236019377080136000000000000)
      constant := (4750902241672842559160037978162393281647412690694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253420647786248888063/50000000000000000000)
  centralHi := (506841295572497776127/100000000000000000000)
  directionLo := (127323936798576436769/25000000000000000000)
  directionHi := (509295747194305747077/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree105.table
  base := (3599144161066702367049766969836147246103/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-78447186170012127848227834584000000000000)
      constant := (2216114272849540995336963858637378355937648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree105.table
  base := (28793153285490218713665902955833380232627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-3496306929149651256169412123179264000000000000)
      constant := (98870639361898043914558886525346885842673573334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127323936798576436769/25000000000000000000)
  centralHi := (509295747194305747077/100000000000000000000)
  directionLo := (511738426662298174039/100000000000000000000)
  directionHi := (12793460666557454351/2500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree106.table
  base := (745152477215626168618675474718832263447/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-34924499375409108808399061448744000000000000)
      constant := (996407355218524147534472940989504402254410160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree106.table
  base := (7451524771509423528944196934942298558047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-172949719892054969496366368694487736000000000000)
      constant := (4939343616853589101573786638922524397048301710904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511738426662298174039/100000000000000000000)
  centralHi := (12793460666557454351/2500000000000000000)
  directionLo := (514169501755406009159/100000000000000000000)
  directionHi := (12854237543885150229/2500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree107.table
  base := (12333862668499530341448287968262884932519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-35253789649842869235729647845944000000000000)
      constant := (1015694571084440505434342778598147661276204395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree107.table
  base := (7708664167262318949062367573091651640177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-174580400255777027440431543353191536000000000000)
      constant := (5034949106032183220857287619665442823687549525064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514169501755406009159/100000000000000000000)
  centralHi := (12854237543885150229/2500000000000000000)
  directionLo := (64573642038083227263/12500000000000000000)
  directionHi := (103317827260933163621/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree108.table
  base := (31878826035943026291766206181968777899781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-3953675547141847740340026027016000000000000)
      constant := (115018671324887692267618377770280940234178538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree108.table
  base := (31878826034073234567452168941284911137837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-176211080619499085384496718011895336000000000000)
      constant := (5131477796266815589017958035890993189819228825546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64573642038083227263/12500000000000000000)
  centralHi := (103317827260933163621/20000000000000000000)
  directionLo := (518997490322061900453/100000000000000000000)
  directionHi := (259498745161030950227/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree109.table
  base := (65877214364664510700535415364735356302397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-35912370198710390090390820640344000000000000)
      constant := (1054827767736839226087877095772984292129357077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree109.table
  base := (65877214361485709971644157462238306409443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-177841760983221143328561892670599136000000000000)
      constant := (5228929687555886205306037642936056264343085778347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518997490322061900453/100000000000000000000)
  centralHi := (259498745161030950227/50000000000000000000)
  directionLo := (130348680031003016403/25000000000000000000)
  directionHi := (521394720124012065613/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree110.table
  base := (68028000220227015548769076035434133289277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-36241660473144150517721407037544000000000000)
      constant := (1074673748522723241837596580711066452780571157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree110.table
  base := (17007000054381256511705476268763508943461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-179472441346943201272627067329302936000000000000)
      constant := (5327304779898105244941394617598793315607678127476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130348680031003016403/25000000000000000000)
  centralHi := (521394720124012065613/100000000000000000000)
  directionLo := (261890489224883369433/50000000000000000000)
  directionHi := (523780978449766738867/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree111.table
  base := (17552502409522141597589577298587517803667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4063438971953101216116888159416000000000000)
      constant := (121633998253491932481368993575739153489518732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree111.table
  base := (70210009635791973993567629831344013492663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-181103121710665259216692241988006736000000000000)
      constant := (5426603073292442059018344522784806900410635621727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261890489224883369433/50000000000000000000)
  centralHi := (523780978449766738867/100000000000000000000)
  directionLo := (263078207287487585881/50000000000000000000)
  directionHi := (526156414574975171763/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree112.table
  base := (36211621308932608110650592763689603553149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-753066143306360640252705710856000000000000)
      constant := (22753560714546578713128272027698412863956682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree112.table
  base := (36211621307956644147603774083357034971831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-3729261266824230962464437074422664000000000000)
      constant := (112792338117103721591582928900176485107961775902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263078207287487585881/50000000000000000000)
  centralHi := (526156414574975171763/100000000000000000000)
  directionLo := (528521174420657702567/100000000000000000000)
  directionHi := (66065146802582212821/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree113.table
  base := (37333849579628657937007685510663376663867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-37229531296445431799713166229144000000000000)
      constant := (1135329220716655990387585932937957098217530694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree113.table
  base := (1866692478939960135850856392550637633411/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-184364482438109375104822591305414336000000000000)
      constant := (5627969263234392269108830881402497856631098616760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528521174420657702567/100000000000000000000)
  centralHi := (66065146802582212821/12500000000000000000)
  directionLo := (53087540065780917501/10000000000000000000)
  directionHi := (530875400657809175011/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree114.table
  base := (76943379262035446932031316467228219792931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4173202396764354691893750291816000000000000)
      constant := (128435580154771902127062186858078182769853619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree114.table
  base := (38471689630312817523232071714780466487559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-185995162801831433048887765964118136000000000000)
      constant := (5730037159780888168424968431691360456552276195422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53087540065780917501/10000000000000000000)
  centralHi := (530875400657809175011/100000000000000000000)
  directionLo := (533219232807845702421/100000000000000000000)
  directionHi := (266609616403922851211/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree115.table
  base := (79250282926028614024152956802569183128111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-37888111845312952654374339023544000000000000)
      constant := (1176697477041580334252509111018893009759496951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree115.table
  base := (79250282924830554898024847301778039443699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-187625843165553490992952940622821936000000000000)
      constant := (5833028257377211364063229905106964634609573235771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533219232807845702421/100000000000000000000)
  centralHi := (266609616403922851211/50000000000000000000)
  directionLo := (535552807339094891553/100000000000000000000)
  directionHi := (267776403669547445777/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree116.table
  base := (10198551268889291972500309127269633186691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-38217402119746713081704925420744000000000000)
      constant := (1197660987662501621430097602643471265882645848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree116.table
  base := (40794205075048137135519051375358908510257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-189256523529275548937018115281525736000000000000)
      constant := (5936942556023106855533169354824635344646944885906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535552807339094891553/100000000000000000000)
  centralHi := (267776403669547445777/50000000000000000000)
  directionLo := (16808633054984948541/3125000000000000000)
  directionHi := (537876257759518353313/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree117.table
  base := (16791552187442066279690432811520857869361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4282965821575608167670612424216000000000000)
      constant := (135423417028408299427003093381174610177993445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree117.table
  base := (83957760936345267232819780960329360318183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-190887203892997606881083289940229536000000000000)
      constant := (6041780055718405517764384305992421871085565441807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16808633054984948541/3125000000000000000)
  centralHi := (537876257759518353313/100000000000000000000)
  directionLo := (270094857352922384379/50000000000000000000)
  directionHi := (540189714705844768759/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree118.table
  base := (8635833528426754819175701298064782763941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-38875982668614233936366098215144000000000000)
      constant := (1240146773821077922256004271909537691988979810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree118.table
  base := (17271667056706504997638977426059501767123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-192517884256719664825148464598933336000000000000)
      constant := (6147540756463009162764945447378587482152650355335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270094857352922384379/50000000000000000000)
  centralHi := (540189714705844768759/100000000000000000000)
  directionLo := (542493306029281895387/100000000000000000000)
  directionHi := (135623326507320473847/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree119.table
  base := (17758026638452863223307303022502140357597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-800107611082612129871360910456000000000000)
      constant := (25748347946095954024079512133036596316091865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree119.table
  base := (44395066595819908297206921672266896965599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-3962215604498810668759462025666064000000000000)
      constant := (127637237923609755493970351735131135039610866158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542493306029281895387/100000000000000000000)
  centralHi := (135623326507320473847/25000000000000000000)
  directionLo := (544787156877966642209/100000000000000000000)
  directionHi := (54478715687796664221/10000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree120.table
  base := (18250630932240289888001672711530155248619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4392729246386861643447474556616000000000000)
      constant := (142597508874282947634060701213044888035911655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree120.table
  base := (91253154660670880965784779901743133033857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-195779244984163780713278813916340936000000000000)
      constant := (6361831761100020243633181370103339715264217027353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544787156877966642209/100000000000000000000)
  centralHi := (54478715687796664221/10000000000000000000)
  directionLo := (54707138977630366789/10000000000000000000)
  directionHi := (547071389776303667891/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree121.table
  base := (46873699845549072182275611044864956406757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-39863853491915515218357857406744000000000000)
      constant := (1305272365350620732361203911829554891550759674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree121.table
  base := (93747399690647401355057652177144204671749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-197409925347885838657343988575044736000000000000)
      constant := (6470362064992483138695536210024075205673355924221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54707138977630366789/10000000000000000000)
  centralHi := (547071389776303667891/100000000000000000000)
  directionLo := (549346124701334823027/100000000000000000000)
  directionHi := (137336531175333705757/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree122.table
  base := (96272868281988545524233547595612007584499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-40193143766349275645688443803944000000000000)
      constant := (1327353405804939415927493086742352895344764059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree122.table
  base := (6017054267600352327268017484977303511109/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-199040605711607896601409163233748536000000000000)
      constant := (6579815569934345805485789272835585183220577690576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549346124701334823027/100000000000000000000)
  centralHi := (137336531175333705757/25000000000000000000)
  directionLo := (551611479156274127523/100000000000000000000)
  directionHi := (137902869789068531881/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree123.table
  base := (12353695054239859313704995873367848629227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4502492671198115119224336689016000000000000)
      constant := (149957855692391440347429072902648196662656984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree123.table
  base := (19765912086718721691299974211003694515723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-200671286075329954545474337892452336000000000000)
      constant := (6690192275925713000692797251348160411465953402335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551611479156274127523/100000000000000000000)
  centralHi := (137902869789068531881/25000000000000000000)
  directionLo := (553867568241335812097/100000000000000000000)
  directionHi := (276933784120667906049/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree124.table
  base := (101417476146945030589410549865426835570059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-40851724315216796500349616598344000000000000)
      constant := (1372074251630396025536779890668349234486396019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree124.table
  base := (101417476146668743280285453896865030773907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-202301966439052012489539512551156136000000000000)
      constant := (6801492182966710005741189508978554057719170563803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553867568241335812097/100000000000000000000)
  centralHi := (276933784120667906049/50000000000000000000)
  directionLo := (889783207555161963/160000000000000000)
  directionHi := (139028626180494056719/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree125.table
  base := (104036615421130588096029026852346280018699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-41181014589650556927680202995544000000000000)
      constant := (1394714057001586639437873115579884709488246259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree125.table
  base := (6502288463805994752092688582976794939951/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-203932646802774070433604687209859936000000000000)
      constant := (6913715291057478345854137068124557801816901841264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (889783207555161963/160000000000000000)
  centralHi := (139028626180494056719/25000000000000000000)
  directionLo := (111670479818932819983/20000000000000000000)
  directionHi := (139588099773666024979/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree126.table
  base := (2133739565130902539275831850780489599041/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-94127675428762624387779567784000000000000)
      constant := (3214376683322280021725999892683024479952050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree126.table
  base := (106686978256345811887734972732107044943697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-4195169942173390375054486976909464000000000000)
      constant := (143405338779554535158845874017388521747938334137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111670479818932819983/20000000000000000000)
  centralHi := (139588099773666024979/25000000000000000000)
  directionLo := (56058135965028768697/10000000000000000000)
  directionHi := (560581359650287686971/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree127.table
  base := (109368564653262843012924917271393197186989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-41839595138518077782341375789944000000000000)
      constant := (1440552432661045296323378363570892399959462149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree127.table
  base := (109368564653093566276630882702808038481217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-207194007530218186321735036527267536000000000000)
      constant := (7140931110388955546656424990053864799379890840793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56058135965028768697/10000000000000000000)
  centralHi := (560581359650287686971/100000000000000000000)
  directionLo := (562801492535301765143/100000000000000000000)
  directionHi := (70350186566912720643/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree128.table
  base := (56040687305680696535657965758234544510319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-42168885412951838209671962187144000000000000)
      constant := (1463751002949380306325608484608874868258101358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree128.table
  base := (2802034365280440869948027804810238687789/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-208824687893940244265800211185971336000000000000)
      constant := (7255923821629999470634773313634889855773345975240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562801492535301765143/100000000000000000000)
  centralHi := (70350186566912720643/12500000000000000000)
  directionLo := (565012901810712163951/100000000000000000000)
  directionHi := (35313306363169510247/6250000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree129.table
  base := (114825408130920937171001680308704283468861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4722019520820622070778060953816000000000000)
      constant := (165237314245573985573553850294150509889974189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree129.table
  base := (114825408130798856488210745687329789418867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-210455368257662302209865385844675136000000000000)
      constant := (7371839733921480347421178850949684182181151507643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565012901810712163951/100000000000000000000)
  centralHi := (35313306363169510247/6250000000000000000)
  directionLo := (567215689508990575631/100000000000000000000)
  directionHi := (35450980594311910977/6250000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree130.table
  base := (7350041575751459129126568377276121407549/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-42827465961819359064333134981544000000000000)
      constant := (1510706908443438092835039799987580312651665744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree130.table
  base := (58800332605959839634599868701788806500361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-212086048621384360153930560503378936000000000000)
      constant := (7488678847263578039547819781419143346511852063938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567215689508990575631/100000000000000000000)
  centralHi := (35450980594311910977/6250000000000000000)
  directionLo := (569409955689007722329/100000000000000000000)
  directionHi := (56940995568900772233/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree131.table
  base := (120407145854751547372552699914534210132543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-43156756236253119491663721378744000000000000)
      constant := (1534464243649233545423503365131333586668451463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree131.table
  base := (120407145854663521336455574866620712280733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-213716728985106418097995735162082736000000000000)
      constant := (7606441161656474526227454250537213361841075180757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569409955689007722329/100000000000000000000)
  centralHi := (56940995568900772233/10000000000000000000)
  directionLo := (571595798489068562057/100000000000000000000)
  directionHi := (285797899244534281029/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree132.table
  base := (123244850059188987883372658600288124442471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4831782945631875546554923086216000000000000)
      constant := (173156425980843225329221658547606118097681079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree132.table
  base := (30811212514778561610708781470073421315171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-215347409348828476042060909820786536000000000000)
      constant := (7725126677100352758668988348267125714913054705836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571595798489068562057/100000000000000000000)
  centralHi := (285797899244534281029/50000000000000000000)
  directionLo := (573773314178129070903/100000000000000000000)
  directionHi := (71721664272266133863/12500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree133.table
  base := (126113777825419193184840710979146238985507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-894190546635115109108671309656000000000000)
      constant := (32296687326092681127287701369580316150869563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree133.table
  base := (31528444456338933636244061097586448034029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-4428124279847970081349511928152864000000000000)
      constant := (160096640685620320886333597867128507011692020436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573773314178129070903/100000000000000000000)
  centralHi := (71721664272266133863/12500000000000000000)
  directionLo := (17998206162664694671/3125000000000000000)
  directionHi := (575942597205270229473/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree134.table
  base := (32253482288381352178102609669788507316409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-44144627059554400773655480570344000000000000)
      constant := (1606853779102127298482845715172242926906145476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree134.table
  base := (129013929153471532238592310858163583950639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-218608770076272591930191259138194136000000000000)
      constant := (7965267311141785679832928107368274889132253547031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17998206162664694671/3125000000000000000)
  centralHi := (575942597205270229473/100000000000000000000)
  directionLo := (144525935061875288059/25000000000000000000)
  directionHi := (578103740247501152237/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree135.table
  base := (131945304043590308911335435235775156488359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-4941546370443129022331785218616000000000000)
      constant := (181261792688709250792288533985112982667929591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree135.table
  base := (65972652021772284947780964051132014664771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-220239450439994649874256433796897936000000000000)
      constant := (8086722429739703542887967740432136355639246429718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144525935061875288059/25000000000000000000)
  centralHi := (578103740247501152237/100000000000000000000)
  directionLo := (58025683425595981517/10000000000000000000)
  directionHi := (580256834255959815171/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree136.table
  base := (8431743905980985206115102912823445763553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-44803207608421921628316653364744000000000000)
      constant := (1656044744267345355637006281357426233307629968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree136.table
  base := (33726975623914233626940330868679040094311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-221870130803716707818321608455601736000000000000)
      constant := (8209100749389328387748765949060013046631608726076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58025683425595981517/10000000000000000000)
  centralHi := (580256834255959815171/100000000000000000000)
  directionLo := (9100030757821508547/1562500000000000000)
  directionHi := (582401968500576547009/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree137.table
  base := (689508622549613250034157520107159856471/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-45132497882855682055647239761944000000000000)
      constant := (1680919609309049261259566113820699499340742200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree137.table
  base := (137901724509889689002072760194580841698423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-223500811167438765762386783114305536000000000000)
      constant := (8332402270090837055541141270049919591009519028767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9100030757821508547/1562500000000000000)
  centralHi := (582401968500576547009/100000000000000000000)
  directionLo := (146134807653315585111/25000000000000000000)
  directionHi := (116907846122652468089/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree138.table
  base := (70463385043175354459319381881668106863213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5051309795254382498108647351016000000000000)
      constant := (189553414369281126587278165530531474472594874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree138.table
  base := (70463385043161365135421787950729091238501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-225131491531160823706451957773009336000000000000)
      constant := (8456626991844403843652759298535435175360871696058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146134807653315585111/25000000000000000000)
  centralHi := (116907846122652468089/20000000000000000000)
  directionLo := (586668706629681100603/100000000000000000000)
  directionHi := (146667176657420275151/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree139.table
  base := (14398303922505842772461454789981297317317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-45791078431723202910308412556344000000000000)
      constant := (1731228104310822602786704254052073521169367970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree139.table
  base := (143983039225034679406683266699671551085889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-226762171894882881650517132431713136000000000000)
      constant := (8581774914650200266277159335943528253168848344281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586668706629681100603/100000000000000000000)
  centralHi := (146667176657420275151/25000000000000000000)
  directionLo := (588790481029662168407/100000000000000000000)
  directionHi := (73598810128707771051/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree140.table
  base := (147070531926122955357331708754453806398313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-941232014411366598727326509256000000000000)
      constant := (35850239474917564784539449684230084257584817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree140.table
  base := (29414106385220559735444024677262235123289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-4661078617522549787644536879396264000000000000)
      constant := (177711143643028466801873025711601719849619747845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588790481029662168407/100000000000000000000)
  centralHi := (73598810128707771051/12500000000000000000)
  directionLo := (590904636776306826649/100000000000000000000)
  directionHi := (11818092735526136533/2000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree141.table
  base := (150189248189620038107860315047218924758351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5161073220065635973885509483416000000000000)
      constant := (198031291022664195374116859056209727313159199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree141.table
  base := (7509462409480146532785269070166771197067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-230023532622326997538647481749120736000000000000)
      constant := (8834840363419153117469598264712763230055327508860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590904636776306826649/100000000000000000000)
  centralHi := (11818092735526136533/2000000000000000000)
  directionLo := (7412640691923000091/1250000000000000000)
  directionHi := (593011255353840007281/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree142.table
  base := (38334797003905993626684795324550380507257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-46778949255024484192300171747944000000000000)
      constant := (1808087759109906620212527962191274871214801348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree142.table
  base := (15333918801560945566357105798760779727323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-231654212986049055482712656407824536000000000000)
      constant := (8962757889382637261638852617607082722377672168670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7412640691923000091/1250000000000000000)
  centralHi := (593011255353840007281/100000000000000000000)
  directionLo := (297555208402128030681/50000000000000000000)
  directionHi := (595110416804256061363/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree143.table
  base := (78260175702103792839766999242418474121051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-47108239529458244619630758145144000000000000)
      constant := (1834080153988779374095236196304485094174766982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree143.table
  base := (15652035140419526430344041290435034793619/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-233284893349771113426777831066528336000000000000)
      constant := (9091598616399006318762991435803807848182888634510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297555208402128030681/50000000000000000000)
  centralHi := (595110416804256061363/100000000000000000000)
  directionLo := (597202199762805220351/100000000000000000000)
  directionHi := (583205273205864473/97656250000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree144.table
  base := (159732738355442198421236316285643561829539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5270836644876889449662371615816000000000000)
      constant := (206695422648958608347974189694860534529647411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree144.table
  base := (9983296147214483899021987361914104428909/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-234915573713493171370843005725232136000000000000)
      constant := (9221362544468416019054620345511388133131094749776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597202199762805220351/100000000000000000000)
  centralHi := (583205273205864473/97656250000000000)
  directionLo := (149821670373091315371/25000000000000000000)
  directionHi := (119857336298473052297/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree145.table
  base := (32595269773879527736442143715875486635587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-47766820078325765474291930939544000000000000)
      constant := (1886623708665481716566233276529585448031469335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree145.table
  base := (6519053954775550639232601193186234240271/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-236546254077215229314908180383935936000000000000)
      constant := (9352049673591018799196688673699720879898603858975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149821670373091315371/25000000000000000000)
  centralHi := (119857336298473052297/20000000000000000000)
  directionLo := (300681968958370442089/50000000000000000000)
  directionHi := (601363937916740884179/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree146.table
  base := (10390698934133889595962305487863371821259/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-48096110352759525901622517336744000000000000)
      constant := (1913174868463372230637799304087947951570803504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree146.table
  base := (166251182946134704737006622051866772019729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-238176934440937287258973355042639736000000000000)
      constant := (9483660003766963809550687164663558003297427385641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300681968958370442089/50000000000000000000)
  centralHi := (601363937916740884179/100000000000000000000)
  directionLo := (603434043652931402061/100000000000000000000)
  directionHi := (301717021826465701031/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree147.table
  base := (6782289623429712800453744800852389705379/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-109808164687513120927331300984000000000000)
      constant := (4398894066290994314006661698389309742634475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree147.table
  base := (5298663768304263494939369761283334479209/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-4894032955197129493939561830639664000000000000)
      constant := (196248847652987692569577681416010948699163644448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603434043652931402061/100000000000000000000)
  centralHi := (301717021826465701031/50000000000000000000)
  directionLo := (605497072042405550529/100000000000000000000)
  directionHi := (60549707204240555053/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree148.table
  base := (172894521788264759453924181877615862864283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-48754690901627046756283690131144000000000000)
      constant := (1966835952978379326436296901828220595523148803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree148.table
  base := (172894521788259339331385824740177587247867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-241438295168381403147103704360047336000000000000)
      constant := (9749650267279460832920343177015156039731252048643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605497072042405550529/100000000000000000000)
  centralHi := (60549707204240555053/10000000000000000000)
  directionLo := (607553095181420496901/100000000000000000000)
  directionHi := (303776547590710248451/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree149.table
  base := (176263026553771956273278345469241534578533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-49083981176060807183614276528344000000000000)
      constant := (1993945877695552914360748222097231516749133053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree149.table
  base := (88131513276883678850078231164199193537737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-243068975532103461091168879018751136000000000000)
      constant := (9884030200616294966786820958977610238958371719746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607553095181420496901/100000000000000000000)
  centralHi := (303776547590710248451/50000000000000000000)
  directionLo := (15240054598760512853/2500000000000000000)
  directionHi := (609602183950420514121/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree150.table
  base := (179662754882326880160397608473628415136983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5490363494499396401216095880616000000000000)
      constant := (224582450820652978376002113363607792341712167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree150.table
  base := (179662754882322978775121144325787417457381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-244699655895825519035234053677454936000000000000)
      constant := (10019333335007035665249782641359403099018382915549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15240054598760512853/2500000000000000000)
  centralHi := (609602183950420514121/100000000000000000000)
  directionLo := (76455551005318654313/12500000000000000000)
  directionHi := (122328881608509846901/20000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree151.table
  base := (36618741354798118197099869089993717243577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-49742561724928328038275449322744000000000000)
      constant := (2048724492049377926908875158534540146522087285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree151.table
  base := (183093706773987281225402206947026803503173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-246330336259547576979299228336158736000000000000)
      constant := (10155559670451816173197200005160613901619473491517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76455551005318654313/12500000000000000000)
  centralHi := (122328881608509846901/20000000000000000000)
  directionLo := (76709979498913491589/12500000000000000000)
  directionHi := (613679835991307932713/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree152.table
  base := (93277941114411382867353134077388711349183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-50071851999362088465606035719944000000000000)
      constant := (2076393181686082596486196752768064843409979406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree152.table
  base := (11659742639301247374907106724590534186559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-247961016623269634923364402994862536000000000000)
      constant := (10292709206950766712525170444509913047255517899376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76709979498913491589/12500000000000000000)
  centralHi := (613679835991307932713/100000000000000000000)
  directionLo := (615708535197390892551/100000000000000000000)
  directionHi := (76963566899673861569/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree153.table
  base := (190049281246881726950585884752775721407551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5600126919310649876992958013016000000000000)
      constant := (233805347366224059373028452674854010348969999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree153.table
  base := (47512320311719836297132637705576862119729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-249591696986991692867429577653566336000000000000)
      constant := (10430781944504014545114665091871184043772761142564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615708535197390892551/100000000000000000000)
  centralHi := (76963566899673861569/12500000000000000000)
  directionLo := (617730571954727586343/100000000000000000000)
  directionHi := (77216321494340948293/12500000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree154.table
  base := (96786951914112236117599850298835091352641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-1035314949963869577964636908456000000000000)
      constant := (43516108691412344417644127475763031644347538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree154.table
  base := (193573903828222451902426141480565378764447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-5126987292871709200234586781883064000000000000)
      constant := (215709752716564980367057357798914587227971944887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617730571954727586343/100000000000000000000)
  centralHi := (77216321494340948293/12500000000000000000)
  directionLo := (19367062858617504207/3125000000000000000)
  directionHi := (4957968091806081077/800000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree155.table
  base := (197129749972906704452316356039892947729979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-51059722822663369747597794911544000000000000)
      constant := (2160516780435672187771037239878712789948920739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree155.table
  base := (197129749972904990770897121946911096803077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-252853057714435808755559926970973936000000000000)
      constant := (10709697022773896729858137780888543748097719764733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19367062858617504207/3125000000000000000)
  centralHi := (4957968091806081077/800000000000000000)
  directionLo := (621754917915983314277/100000000000000000000)
  directionHi := (310877458957991657139/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree156.table
  base := (100358409840491431165378963394333748680507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5709890344121903352769820145416000000000000)
      constant := (243214498885049163972899065573380707370689686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree156.table
  base := (200716819680981408813859683101690864968337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-254483738078157866699625101629677736000000000000)
      constant := (10850539363490771398484557586071381866963511247273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621754917915983314277/100000000000000000000)
  centralHi := (310877458957991657139/50000000000000000000)
  directionLo := (623757354397773241491/100000000000000000000)
  directionHi := (155939338599443310373/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree157.table
  base := (204335112952506151225495260350856852338241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-51718303371530890602258967705944000000000000)
      constant := (2217530454468539203981267440908055871881164281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree157.table
  base := (25541889119063114803027048202604805736753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-256114418441879924643690276288381536000000000000)
      constant := (10992304905262424128243346277984138236032744282696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623757354397773241491/100000000000000000000)
  centralHi := (155939338599443310373/25000000000000000000)
  directionLo := (156438345758382442259/25000000000000000000)
  directionHi := (625753383033529769037/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree158.table
  base := (103992314893764286919393782661684161123413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-52047593645964651029589554103144000000000000)
      constant := (2246316673944985305638261103112837430110850266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree158.table
  base := (41596925957505505655624811857139921028043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-257745098805601982587755450947085336000000000000)
      constant := (11134993648088968377569791589342882301901928088735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156438345758382442259/25000000000000000000)
  centralHi := (625753383033529769037/100000000000000000000)
  directionLo := (627743064948156602299/100000000000000000000)
  directionHi := (6277430649481566023/1000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree159.table
  base := (211665370186100960741805192534634335458757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5819653768933156828546682277816000000000000)
      constant := (252809905377200355223217633498901082437479093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree159.table
  base := (211665370186100074017246273494039677793129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-259375779169324040531820625605789136000000000000)
      constant := (11278605591970515045890416205032351678256366914241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627743064948156602299/100000000000000000000)
  centralHi := (6277430649481566023/1000000000000000000)
  directionLo := (157431615075225538127/25000000000000000000)
  directionHi := (629726460300902152509/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree160.table
  base := (215377334148273000568987538921055070327897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-52706174194832171884250726897544000000000000)
      constant := (2304447877818014790781148010088825286014602577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree160.table
  base := (107688667074136124289764761704490754104371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-261006459533046098475885800264492936000000000000)
      constant := (11423140736907172539790445604699258580621108726518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157431615075225538127/25000000000000000000)
  centralHi := (629726460300902152509/100000000000000000000)
  directionLo := (631703628306583206019/100000000000000000000)
  directionHi := (31585181415329160301/5000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree161.table
  base := (219120521674093269783884210444615181222777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1314)
      previous := (657)
      next := (657)
      square := (6414745605852475857089345400000000000000)
      linear := (-1082356417740121067583292108056000000000000)
      constant := (47628425759482479779086824594657536631004993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree161.table
  base := (54780130418523158020223659722911807809237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-5359941630546288906529611733126464000000000000)
      constant := (236093858834674425269420090620198100381900161908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631703628306583206019/100000000000000000000)
  centralHi := (31585181415329160301/5000000000000000000)
  directionLo := (316837313628106296469/50000000000000000000)
  directionHi := (633674627256212592939/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree162.table
  base := (222894932763609261937260205898923729836037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-5929417193744410304323544410216000000000000)
      constant := (262591566842744921871907250122919262761965813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree162.table
  base := (222894932763608721171720225447735963719991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-264267820260490214364016149581900536000000000000)
      constant := (11714980629946241556444036500993938981198108246239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316837313628106296469/50000000000000000000)
  centralHi := (633674627256212592939/100000000000000000000)
  directionLo := (127127902907410236889/20000000000000000000)
  directionHi := (317819757268525592223/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree163.table
  base := (226700567416867416356532780785484007408271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-53694045018133453166242486089144000000000000)
      constant := (2393041595928223633540271557669150447267047511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree163.table
  base := (113350283708433478904908298147648110352009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-265898500624212272308081324240604336000000000000)
      constant := (11862285378048858008995581761296210927056215683522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127127902907410236889/20000000000000000000)
  centralHi := (317819757268525592223/50000000000000000000)
  directionLo := (6375983466521037337/1000000000000000000)
  directionHi := (637598346652103733701/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree164.table
  base := (230537425633913146220752747426223073896969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-54023335292567213593573072486344000000000000)
      constant := (2422945345245219546466534733060820375588563329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree164.table
  base := (46107485126782551481267658874163298413501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-267529180987934330252146498899308136000000000000)
      constant := (12010513327206995270892700780194217555123532115145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6375983466521037337/1000000000000000000)
  centralHi := (637598346652103733701/100000000000000000000)
  directionLo := (639551179239077298197/100000000000000000000)
  directionHi := (319775589619538649099/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree165.table
  base := (234405507414790865987854242453275894824109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (7154)
      previous := (3577)
      next := (3577)
      square := (34924726076307924110819769400000000000000)
      linear := (-6039180618555663780100406542616000000000000)
      constant := (272559483281745735822433747948450518846381341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree165.table
  base := (234405507414790536313258460886055983765571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-269159861351656388196211673558011936000000000000)
      constant := (12159664477420750237695297172462506714208122338059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639551179239077298197/100000000000000000000)
  centralHi := (319775589619538649099/50000000000000000000)
  directionLo := (32074903354441011993/5000000000000000000)
  directionHi := (641498067088820239861/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree166.table
  base := (7447025398735750567225053048080129691399/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-54681915841434734448234245280744000000000000)
      constant := (2483311608799719019485952267462170790205022688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree166.table
  base := (14894050797471483664440459156883812680061/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-270790541715378446140276848216715736000000000000)
      constant := (12309738828690217683968425703573046847873932692304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32074903354441011993/5000000000000000000)
  centralHi := (641498067088820239861/100000000000000000000)
  directionLo := (643439064163259091297/100000000000000000000)
  directionHi := (321719532081629545649/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree167.table
  base := (242235341668215099310920122055781761536641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-55011206115868494875564831677944000000000000)
      constant := (2513774123037260478719335469972967756837658681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree167.table
  base := (121117670834107431161705930722359202537379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-272421222079100504084342022875419536000000000000)
      constant := (12460736381015490320252353945631126419504331744982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643439064163259091297/100000000000000000000)
  centralHi := (321719532081629545649/50000000000000000000)
  directionLo := (645374223612849900641/100000000000000000000)
  directionHi := (322687111806424950321/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree168.table
  base := (246197094140845685552406881304021334108741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (712749511761386206343260600000000000000)
      linear := (-125488653946263617466883034184000000000000)
      constant := (5769666422331869240715903803096021334108741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree168.table
  base := (61549273535211371158164706709111857617031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6500066)
      previous := (3250033)
      next := (3250033)
      square := (31732321013128675292608305172600000000000000)
      linear := (-5592895968220868612824636684369864000000000000)
      constant := (257401166008095078540957433793183588051871348604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell121.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645374223612849900641/100000000000000000000)
  centralHi := (322687111806424950321/50000000000000000000)
  directionLo := (129460719558712004357/20000000000000000000)
  directionHi := (323651798896780010893/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree169.table
  base := (125095035088738228565021884796602700747359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (64386)
      previous := (32193)
      next := (32193)
      square := (314322534686771316997377924600000000000000)
      linear := (-55669786664736015730226004472344000000000000)
      constant := (2575257916433018528787268960329979582059170638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 1549
  qDenominator := 2954
  table := BinomialMassData.Q1549_2954.Degree169.table
  base := (62547517544369071698672473446911791183301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (318503234)
      previous := (159251617)
      next := (159251617)
      square := (1554883729643305089337806953457400000000000000)
      linear := (-275682582806544619972472372192827136000000000000)
      constant := (12765501088833812016027981927305246085633261788916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1549_2954.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell121.Kernel169
