import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell112.Parameters
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch000_049
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch050_099
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch100_149
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch000_049
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch050_099
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree000.table
  base := (4991411926349945276214725717/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18119934969788009659907857000000000000)
      linear := (-941787669676742537905322900000000000)
      constant := (9982823852699890552429451434000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree000.table
  base := (4991411926349945276214725717/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18119934969788009659907857000000000000)
      linear := (-941787669676742537905322900000000000)
      constant := (9982823852699890552429451434000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree001.table
  base := (69589031086661356080014226344598989082347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-9575455813471857626925014093366872500000000000)
      constant := (2683652619329054637928282616476959720937491388774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree001.table
  base := (278116531013796222885015124269373399938411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-2130088191732146127494373564758555000000000000)
      constant := (595855643279046710211651398802672529652776813659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4994596141956158837/10000000000000000000)
  directionHi := (49945961419561588371/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree002.table
  base := (81458871787743119422634603863260750314029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-18697362672073088810299405620949972500000000000)
      constant := (1579178008503036335697779709477066209999991430309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree002.table
  base := (20333528449759656939013246948880320467587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-2079693863413187633766526613004802500000000000)
      constant := (175199562988659701994450430725289858055554878412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4994596141956158837/10000000000000000000)
  centralHi := (49945961419561588371/100000000000000000000)
  directionLo := (70634256025307361281/100000000000000000000)
  directionHi := (35317128012653680641/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree003.table
  base := (101136512952934043826040853726697651722819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-6182059895705404443038621588562905000000000000)
      constant := (221395244713568595596021573623230416120318380211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree003.table
  base := (25234391735015972061559051166868820736917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-3094343630960302203785866443630327500000000000)
      constant := (110489998254776328592207636017055921943708604746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70634256025307361281/100000000000000000000)
  centralHi := (35317128012653680641/50000000000000000000)
  directionLo := (43254471405777819039/50000000000000000000)
  directionHi := (86508942811555638079/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree004.table
  base := (33447004033538309502396838502107170788093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-36941176389275551177048188676116172500000000000)
      constant := (683390600722671010059019281225648547292858436853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree004.table
  base := (66748598641253308606729954976573620281177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-8217986797014833547610412548511705000000000000)
      constant := (151572062097253403551742928204922673067602534313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43254471405777819039/50000000000000000000)
  centralHi := (86508942811555638079/100000000000000000000)
  directionLo := (99891922839123176741/100000000000000000000)
  directionHi := (49945961419561588371/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree005.table
  base := (46962199680542941069607257565472653389327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-92126166495753564720845160407398545000000000000)
      constant := (1026212240678883432501086441689288588960343974967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree005.table
  base := (23429081797540172411715360397766477526069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-5123643166054531343824546104881377500000000000)
      constant := (56915037763330926477182859982799300235994779461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99891922839123176741/100000000000000000000)
  centralHi := (49945961419561588371/50000000000000000000)
  directionLo := (111682564935721606029/100000000000000000000)
  directionHi := (11168256493572160603/10000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree006.table
  base := (6922379057735078162187932658076747085849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-2452666226954578379724309854723661000000000000)
      constant := (18693860551882841857425895531857025083391538281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree006.table
  base := (17268176293244629393081816409374928492573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-6138292933601645913843885935506902500000000000)
      constant := (46674773870529185134573386237687258822719979437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111682564935721606029/100000000000000000000)
  centralHi := (11168256493572160603/10000000000000000000)
  directionLo := (15292765023832556491/12500000000000000000)
  directionHi := (122342120190660451929/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree007.table
  base := (26399218650630053262569701359436048990331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (356173595736889522479495795727650000000000000)
      linear := (-2624771304697112029680463806484305000000000000)
      constant := (15213778783698484254617390610183344503519835699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree007.table
  base := (1053694258653659394334617600124779626557/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17472400000000000000000000000000000000000000
      center := (174724)
      previous := (87362)
      next := (87362)
      square := (1582993758830620099908870203234000000000000)
      linear := (-11678273797793894667531797169195800000000000)
      constant := (67563981634865626859690478908058098867636317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15292765023832556491/12500000000000000000)
  centralHi := (122342120190660451929/100000000000000000000)
  directionLo := (66072296454093266309/50000000000000000000)
  directionHi := (132144592908186532619/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree008.table
  base := (20542513746855616444441428195102556816767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-146857607647360951821091509572897145000000000000)
      constant := (704645935562177768534383725493750139882120903207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree008.table
  base := (20497755408312110048333879509224166538339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-16335184937391750107765131193515905000000000000)
      constant := (78272590146366693161151131915246960109498107091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66072296454093266309/50000000000000000000)
  centralHi := (132144592908186532619/100000000000000000000)
  directionLo := (70634256025307361281/50000000000000000000)
  directionHi := (141268512050614722563/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree009.table
  base := (8052221246179680890731283205258002451589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-9172301186920189677102238479336852500000000000)
      constant := (38926655883380221287994161766311100449305096341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree009.table
  base := (4016916986845175713984494772196181977007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-9182242236242989623901905427383477500000000000)
      constant := (38934347182811477546866914646962437143888991166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70634256025307361281/50000000000000000000)
  centralHi := (141268512050614722563/100000000000000000000)
  directionLo := (18729735532335595639/12500000000000000000)
  directionHi := (149837884258684765113/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree010.table
  base := (786192594186236323572428752762020449227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-91672617540882938277294537841614772500000000000)
      constant := (361915503471884105059151568988150842176191222936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree010.table
  base := (12547806447580484189619861094333585116731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-20393784007580208387842490516018005000000000000)
      constant := (80474828537372599703450285775972356242712413739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18729735532335595639/12500000000000000000)
  centralHi := (149837884258684765113/100000000000000000000)
  directionLo := (78971499006355682759/50000000000000000000)
  directionHi := (157942998012711365519/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree011.table
  base := (4841521275168112025628851824963331826139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72117794178130523146674768556425000000000000)
      linear := (-833012598342844375708007680737172500000000000)
      constant := (3176200578714350475293309660434972390053154939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree011.table
  base := (4827897361283094213322012074808673117449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-92657370011051394743310620567227500000000000)
      constant := (353250427380264451052197268661980618774555361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78971499006355682759/50000000000000000000)
  centralHi := (157942998012711365519/100000000000000000000)
  directionLo := (82826006911126171037/50000000000000000000)
  directionHi := (6626080552890093683/4000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree012.table
  base := (14159125050948619743536842934220780057/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-12212936806453933404893702321864552500000000000)
      constant := (46216347268322123263753411651454630378194184448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree012.table
  base := (7225375284092891089376429089164844861347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-24452383077768666667919849838520105000000000000)
      constant := (92548166657719846688009098240045379831036417043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82826006911126171037/50000000000000000000)
  centralHi := (6626080552890093683/4000000000000000000)
  directionLo := (173017885623111276157/100000000000000000000)
  directionHi := (86508942811555638079/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree013.table
  base := (2586989193012664466475041376384988739859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-119038338116686631827417712424364072500000000000)
      constant := (455790605691912877840990349115364512677289411739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree013.table
  base := (1288123742500672731198235772404275418161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-13240841306431447903979264749885577500000000000)
      constant := (50718403034912701678274176650255265644987682818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173017885623111276157/100000000000000000000)
  centralHi := (86508942811555638079/50000000000000000000)
  directionLo := (11255170306285967889/6250000000000000000)
  directionHi := (7203308996023019449/4000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree014.table
  base := (338681407641569140993519718420043146079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35617359573688952247949579572765000000000000)
      linear := (-523103040715460665350171852865090500000000000)
      constant := (2053791535090424187967435343869195141974891191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree014.table
  base := (3367592797285013898103211052365526590613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-581856778529737243836677737980045000000000000)
      constant := (2285788479401945057632230747868183567004566453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11255170306285967889/6250000000000000000)
  centralHi := (7203308996023019449/4000000000000000000)
  directionLo := (93440337742514454297/50000000000000000000)
  directionHi := (37376135097005781719/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree015.table
  base := (1838368935655731025116718939966357982377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-30507144851975354265370332328784505000000000000)
      constant := (123918724088162401491756597825830303668382277113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree015.table
  base := (1821159308930633862628000445294462085103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-30540281683051354088035888822273255000000000000)
      constant := (124142686413340179731960276019604912518629823007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93440337742514454297/50000000000000000000)
  centralHi := (37376135097005781719/20000000000000000000)
  directionLo := (96719938394140093063/50000000000000000000)
  directionHi := (193439876788280186127/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree016.table
  base := (245722009360913947072658526306611449917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-146404058692490325377540887007113372500000000000)
      constant := (618798314981217848616537422739556560782026594357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree016.table
  base := (95209901181500843837981725160577464087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-6513916243629116645614913696704861000000000000)
      constant := (27554890966665359306611304661192196026230428103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96719938394140093063/50000000000000000000)
  centralHi := (193439876788280186127/100000000000000000000)
  directionLo := (99891922839123176741/50000000000000000000)
  directionHi := (199783845678246353483/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree017.table
  base := (-27319784573570360226405179447572858309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7705328400000000000000000000000000000000000000
      center := (77053284)
      previous := (38526642)
      next := (38526642)
      square := (698100247644303464059811759626194000000000000)
      linear := (-12442077244087324524873222282775717800000000000)
      constant := (54911316063840643868622599960500624959506215811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree017.table
  base := (-139348210637379952701464539801493110033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-6919776150647962473622649628955071000000000000)
      constant := (30567372108682975554133641487699364993571777823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99891922839123176741/50000000000000000000)
  centralHi := (199783845678246353483/100000000000000000000)
  directionLo := (205932474505877020037/100000000000000000000)
  directionHi := (102966237252938510019/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree018.table
  base := (-854127099793162815726335899458969682017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-18294208045521420860476630006919952500000000000)
      constant := (84465464273576636137618798396166774520670955727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree018.table
  base := (-537656959454750257600568491210825931/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 428073800000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (38783347091350192447767319979233000000000000)
      linear := (-732563605766680830163038556120528100000000000)
      constant := (3385601091191180174316966017867817145625053504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205932474505877020037/100000000000000000000)
  centralHi := (102966237252938510019/50000000000000000000)
  directionLo := (52975692018980520961/25000000000000000000)
  directionHi := (42380553615184416769/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree019.table
  base := (-2603396238751371094018277734223691960281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5336100)
      previous := (2668050)
      next := (2668050)
      square := (48344892496142899173117157868850000000000000)
      linear := (-962713458550105368020299510193145000000000000)
      constant := (4653783401997008874446011913768219573307445559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree019.table
  base := (-2614283970617464757218582378790698251711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-107084431643845625064239909881655000000000000)
      constant := (518180784560079516524193150113669950065605481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52975692018980520961/25000000000000000000)
  centralHi := (42380553615184416769/20000000000000000000)
  directionLo := (217709398465850247453/100000000000000000000)
  directionHi := (108854699232925123727/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree020.table
  base := (-3384195759499902555071779717115753554441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-365783372253790500222076906234891545000000000000)
      constant := (1851391375763933811225269060766331445123912041439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree020.table
  base := (-3393851881011592023053651398331194959599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-40686779358522499788229287128528505000000000000)
      constant := (206152742070531694747322506824857108575518047969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217709398465850247453/100000000000000000000)
  centralHi := (108854699232925123727/50000000000000000000)
  directionLo := (223365129871443212059/100000000000000000000)
  directionHi := (11168256493572160603/5000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree021.table
  base := (-812760883030961113693627415908031671413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (873620)
      previous := (436810)
      next := (436810)
      square := (7914968794153100499544351016170000000000000)
      linear := (-174161989102491139496066072240389000000000000)
      constant := (922563136205796286647502848873375268561008747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree021.table
  base := (-4072349190241469321193600222618700518493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-871756712114627120985060546730195000000000000)
      constant := (4622864486096142661046491942569637542651707267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223365129871443212059/100000000000000000000)
  centralHi := (11168256493572160603/5000000000000000000)
  directionLo := (28610143607810627387/12500000000000000000)
  directionHi := (228881148862485019097/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree022.table
  base := (-4653236231775991340697709860944923960949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144235588356261046293349537112850000000000000)
      linear := (-3324553716431367148393177457398545000000000000)
      constant := (18416402149677411333638953512588847160492958251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree022.table
  base := (-233039083216933246105362899677207655171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17689000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (1602617648402900514370550412365000000000000)
      linear := (-36979651593975998403559211943000500000000000)
      constant := (205076495925860636900500351167438247575360362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28610143607810627387/12500000000000000000)
  centralHi := (228881148862485019097/100000000000000000000)
  directionLo := (234267324581844665729/100000000000000000000)
  directionHi := (23426732458184466573/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree023.table
  base := (-103234804938091726517402039381305632273/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (349050123822151732029905879813097000000000000)
      linear := (-8410296268107957746446465108007802900000000000)
      constant := (48672240858327918391517455425622948406417241367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree023.table
  base := (-5168390100999384376457959080407546451391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-46774677963805187208345326112281655000000000000)
      constant := (270999564108348605744036735684236970209382696721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234267324581844665729/100000000000000000000)
  centralHi := (23426732458184466573/10000000000000000000)
  directionLo := (59883104059523593127/25000000000000000000)
  directionHi := (239532416238094372509/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree024.table
  base := (-1119419223827582536229561783837107644003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-9750191713835563326423823076790141000000000000)
      constant := (58884088926427502893790852672611137749112942893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree024.table
  base := (-700368244633676260897330146245779079651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-24401988749449708174192002886766352500000000000)
      constant := (147537369073782572619294434298577582308265875124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59883104059523593127/25000000000000000000)
  centralHi := (239532416238094372509/100000000000000000000)
  directionLo := (244684240381320903857/100000000000000000000)
  directionHi := (122342120190660451929/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree025.table
  base := (-238634160882372838755734933375852558469/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7705328400000000000000000000000000000000000000
      center := (77053284)
      previous := (38526642)
      next := (38526642)
      square := (698100247644303464059811759626194000000000000)
      linear := (-18280097633592112482232832860428901800000000000)
      constant := (115070974333326004046645599802301408517540384451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree025.table
  base := (-5970991336297121624277025263927784521337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-50833277033993645488422685434783755000000000000)
      constant := (320354079671883173701383967858651026771850446647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244684240381320903857/100000000000000000000)
  centralHi := (122342120190660451929/50000000000000000000)
  directionLo := (249729807097807941853/100000000000000000000)
  directionHi := (124864903548903970927/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree026.table
  base := (-3136766104177560848094970206596023192347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-237623127278502637211284802282944372500000000000)
      constant := (1557238406487638910404456123001521197922374995613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree026.table
  base := (-196188645675524403485685941342182423097/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-26431288284543937314230682548017402500000000000)
      constant := (173412897171438653936432020219707267088132755312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249729807097807941853/100000000000000000000)
  centralHi := (124864903548903970927/50000000000000000000)
  directionLo := (127337715951748463629/50000000000000000000)
  directionHi := (254675431903496927259/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree027.table
  base := (-6524781222322543734571110000071906460097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-54832229808245304087702043069006105000000000000)
      constant := (373644642298666505554009514112653903641908644207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree027.table
  base := (-816090622858951918093363437085209676879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-27445938052091051884250022378642927500000000000)
      constant := (187239972160298824487582386788370297396432686596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127337715951748463629/50000000000000000000)
  centralHi := (254675431903496927259/100000000000000000000)
  directionLo := (64881707108666728559/25000000000000000000)
  directionHi := (259526828434666914237/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree028.table
  base := (-6723521168840255823451952754263537902721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (356173595736889522479495795727650000000000000)
      linear := (-10443548612069595901144227972984105000000000000)
      constant := (73911709127197567892196781219258769607841195991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree028.table
  base := (-6726969318281174376707588268616745632641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-1161656645699516998133443355480345000000000000)
      constant := (8230778659227564044194132648775861934020608479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64881707108666728559/25000000000000000000)
  centralHi := (259526828434666914237/100000000000000000000)
  directionLo := (66072296454093266309/25000000000000000000)
  directionHi := (264289185816373065237/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree029.table
  base := (-6873056856893265916897378728305252248883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-529977695708612661522815953731387345000000000000)
      constant := (3891029051013002758596876587014253769943794879557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree029.table
  base := (-6876067846476568728539431784784001229629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-58950475174370562048577404079787955000000000000)
      constant := (433303364968237783620864087281623797072140206899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66072296454093266309/25000000000000000000)
  centralHi := (264289185816373065237/100000000000000000000)
  directionLo := (134483616847560380109/50000000000000000000)
  directionHi := (268967233695120760219/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree030.table
  base := (-6976174585647309784137420355697901837253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-60913501047312791543284970754061505000000000000)
      constant := (463423779850414749477769834579852137542500633643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree030.table
  base := (-1744700179894209335624908567534779531863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-30489887354732395594308041870519502500000000000)
      constant := (232229812883724105039709721612374065436331845106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134483616847560380109/50000000000000000000)
  centralHi := (268967233695120760219/100000000000000000000)
  directionLo := (54713059451553260429/20000000000000000000)
  directionHi := (136782648628883151073/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree031.table
  base := (-7035223601918131847952845030648291794073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-566465323143017586256313519841719745000000000000)
      constant := (4460983395859350874156812417415986887069105903567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree031.table
  base := (-27490279413885151548699465093850872541/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-31504537122279510164327381701145027500000000000)
      constant := (248385960273659464144131277105573221229157423488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54713059451553260429/20000000000000000000)
  centralHi := (136782648628883151073/50000000000000000000)
  directionLo := (139043672029559092147/50000000000000000000)
  directionHi := (55617468811823636859/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree032.table
  base := (-1763046177070401602349444654375733718813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-292354568430110024311531151448442972500000000000)
      constant := (2380749512897000225825336020353448693527962884054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree032.table
  base := (-1763543978472773654247085017361280535591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-32519186889826624734346721531770552500000000000)
      constant := (265118010358599146801230176832457186682635253842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139043672029559092147/50000000000000000000)
  centralHi := (55617468811823636859/20000000000000000000)
  directionLo := (2260296192809835561/800000000000000000)
  directionHi := (141268512050614722563/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree033.table
  base := (-1405745614945730075328435911029417323863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35378000000000000000000000000000000000000000
      center := (353780)
      previous := (176890)
      next := (176890)
      square := (3205235296805801028741100824730000000000000)
      linear := (-110735160803934345452674212296061000000000000)
      constant := (931557159859875459741983829040678636958187393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree033.table
  base := (-3515229674305723765736538065335169331773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-277139145928708589292281498862777500000000000)
      constant := (2334084138600262178987891984433493689690267403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2260296192809835561/800000000000000000)
  centralHi := (141268512050614722563/50000000000000000000)
  directionLo := (143458852158121496469/50000000000000000000)
  directionHi := (286917704316242992939/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree034.table
  base := (-3483130982972746511212095724187384915873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-310598382147312486678279934503609172500000000000)
      constant := (2696722698466855677664875366735767930214980405767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree034.table
  base := (-1393553171562916876625980074075473029259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-13819394569968341549754160477208641000000000000)
      constant := (120121187578142788215523892721689412867837943429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143458852158121496469/50000000000000000000)
  centralHi := (286917704316242992939/100000000000000000000)
  directionLo := (145616249189631458533/50000000000000000000)
  directionHi := (291232498379262917067/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree035.table
  base := (-3432986909158059402613845821670941332637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (178086797868444761239747897863825000000000000)
      linear := (-6524903857263545262482741347575352500000000000)
      constant := (58416593227712623580324819296922349504841748827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree035.table
  base := (-3433639531125724897800456160517239848483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-725778289642203437640913082115247500000000000)
      constant := (6505165473269252003030091294462546446178414077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145616249189631458533/50000000000000000000)
  centralHi := (291232498379262917067/100000000000000000000)
  directionLo := (147742146300870856351/50000000000000000000)
  directionHi := (295484292601741712703/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree036.table
  base := (-6728864871079490790411199253040872199233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-73076043525447766454450826124172305000000000000)
      constant := (674050185154504578187355720916538841411799863023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree036.table
  base := (-1682499195427948830780392730565794857561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-36577785960015083014424080854272652500000000000)
      constant := (337773530653868071114335457482207105453034039982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147742146300870856351/50000000000000000000)
  centralHi := (295484292601741712703/100000000000000000000)
  directionLo := (18729735532335595639/6250000000000000000)
  directionHi := (11987030740694781209/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree037.table
  base := (-1311155872960693002148444773024832611633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-135185641089246472091361243634543389000000000000)
      constant := (1283661144856152760146374253873077506430845186807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree037.table
  base := (-3278380101527203245950793850993195527851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-37592435727562197584443420684898177500000000000)
      constant := (357363336111243263477418706938196087581249082981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18729735532335595639/6250000000000000000)
  centralHi := (11987030740694781209/4000000000000000000)
  directionLo := (6076188453252594157/2000000000000000000)
  directionHi := (303809422662629707851/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree038.table
  base := (-3173714580128576478566493941892928267439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2668050)
      previous := (1334025)
      next := (1334025)
      square := (24172446248071449586558578934425000000000000)
      linear := (-961457090254064851556170361811472500000000000)
      constant := (9391100550116346538053477716693381454721187521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree038.table
  base := (-6348278468459438225697782335019321511473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-213889670333015579803117786789605000000000000)
      constant := (2091533327697226743660504108650135442758476583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6076188453252594157/2000000000000000000)
  centralHi := (303809422662629707851/100000000000000000000)
  directionLo := (153943791983246856227/50000000000000000000)
  directionHi := (61577516793298742491/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree039.table
  base := (-3052207248193847773333422593982581549441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-39578657382257626955016876904613852500000000000)
      constant := (397369262361374495855356076943552780911604516271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree039.table
  base := (-6105149403402667053701392019055235247703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-79243470525312853448964200692298455000000000000)
      constant := (796496358969257362414476103833744835188109177593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153943791983246856227/50000000000000000000)
  centralHi := (61577516793298742491/20000000000000000000)
  directionLo := (311912429093245738831/100000000000000000000)
  directionHi := (19494526818327858677/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree040.table
  base := (-582724149310573053737539952079329812791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-73065964659783974755705256733821554500000000000)
      constant := (753511235069267686904958357891063532351337061089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree040.table
  base := (-291393849530509134036953439423955615647/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-8127277006040708258900288035354950500000000000)
      constant := (83908407652515859291850965932134545085786492514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311912429093245738831/100000000000000000000)
  centralHi := (19494526818327858677/6250000000000000000)
  directionLo := (315885996025422731037/100000000000000000000)
  directionHi := (157942998012711365519/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree041.table
  base := (-5516336909453873004356370403517478891193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-748903460315042209923801350393381745000000000000)
      constant := (7927763260951382484563087015726925745008225168047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree041.table
  base := (-1103377220187134962309525727762996758013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-16660413919100262345808312002960111000000000000)
      constant := (176561154917199660998780963113995393392048473203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315885996025422731037/100000000000000000000)
  centralHi := (157942998012711365519/50000000000000000000)
  directionLo := (159905098063740388103/50000000000000000000)
  directionHi := (319810196127480776207/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree042.table
  base := (-2586030293798007238250880000013531544171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-869781489832476952710374300962072500000000000)
      constant := (9445116237557534461232077418840278928619066549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree042.table
  base := (-258626745591155743041399169617841140501/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (436810)
      previous := (218405)
      next := (218405)
      square := (3957484397076550249772175508085000000000000)
      linear := (-174145651286929675243020897298064500000000000)
      constant := (1893185074530365148954591013558097662283551638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159905098063740388103/50000000000000000000)
  centralHi := (319810196127480776207/100000000000000000000)
  directionLo := (5057606638950962663/1562500000000000000)
  directionHi := (323686824892861610433/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree043.table
  base := (-4794715945532953952648679320392848416101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-785391087749447134657298916503714145000000000000)
      constant := (8743594287577419030409321485881608124856304868579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree043.table
  base := (-4795125376377589218038767402709734197841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-87360668665689770009118919337302655000000000000)
      constant := (973648166035734866249724814789026708924701256671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5057606638950962663/1562500000000000000)
  centralHi := (323686824892861610433/100000000000000000000)
  directionLo := (327517571545934599703/100000000000000000000)
  directionHi := (40939696443241824963/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree044.table
  base := (-4384558824526202224026816249352247752319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144235588356261046293349537112850000000000000)
      linear := (-6641610755922723942347501649246945000000000000)
      constant := (75758377113669899702930191410469952805583062881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree044.table
  base := (-4384912049063536051934943228486228128653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16026176484029005143705504123650000000000000)
      linear := (-738760067775074373133533876021105000000000000)
      constant := (8436096432174228427446368426033377110632257083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327517571545934599703/100000000000000000000)
  centralHi := (40939696443241824963/12500000000000000000)
  directionLo := (331304027644504684149/100000000000000000000)
  directionHi := (6626080552890093683/2000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree045.table
  base := (-197090247461181068522424650181747865101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-9131985724265022882119960917933850500000000000)
      constant := (106667737727583583517058165835073320007443275462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree045.table
  base := (-24638184537522523381971170954254263041/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-9141926773587822828919627865980475500000000000)
      constant := (106901873397703080661415359226747342616307165936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331304027644504684149/100000000000000000000)
  centralHi := (6626080552890093683/2000000000000000000)
  directionLo := (335047694807164818089/100000000000000000000)
  directionHi := (33504769480716481809/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree046.table
  base := (-3466636218021906032391451898966362852909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-840122528901054521757545265669212745000000000000)
      constant := (10043589077795608073652864435767710204161938149211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree046.table
  base := (-693379743470395002864104072199170378659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-18689713454194491485846991664211161000000000000)
      constant := (223680195174619313799244489534546214895800014829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335047694807164818089/100000000000000000000)
  centralHi := (33504769480716481809/10000000000000000000)
  directionLo := (169374995835955220581/50000000000000000000)
  directionHi := (338749991671910441163/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree047.table
  base := (-2959206007088693313118197089907736883501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-858366342618256984124294048724378945000000000000)
      constant := (10497238723158963592075785927707051094029580633179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree047.table
  base := (-1479716067538145775935869747663195896009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-47738933403033343284636818991153427500000000000)
      constant := (584457033774695628805774658536287378063255112679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169374995835955220581/50000000000000000000)
  centralHi := (338749991671910441163/100000000000000000000)
  directionLo := (42801532522183808461/12500000000000000000)
  directionHi := (342412260177470467689/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree048.table
  base := (-2419643642704943475289964716147825752673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-97401128481717716276782536864393905000000000000)
      constant := (1217893648924325022008456854995444034341577043663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree048.table
  base := (-1209919175351392061275909077808603684529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-48753583170580457854656158821778952500000000000)
      constant := (610278866907702922717892692273868896740348348799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42801532522183808461/12500000000000000000)
  centralHi := (342412260177470467689/100000000000000000000)
  directionLo := (173017885623111276157/50000000000000000000)
  directionHi := (69207154249244510463/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree049.table
  base := (-924029086168323523275885849703437929501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (178086797868444761239747897863825000000000000)
      linear := (-9131162959721039886303996069741952500000000000)
      constant := (116683666618970931423845473495000172150213201371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree049.table
  base := (-1848225753317865064764795834700075230183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-2031356446454186629578591781730795000000000000)
      constant := (25986362095479588513848839479448721013870376377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173017885623111276157/50000000000000000000)
  centralHi := (69207154249244510463/20000000000000000000)
  directionLo := (69924345987386223719/20000000000000000000)
  directionHi := (87405432484232779649/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree050.table
  base := (-1244541544396314157450304178284909528129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-913097783769864371224540397889877545000000000000)
      constant := (11919106416947856213397547329786010058303692543591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree050.table
  base := (-1244685717666744186399687544366519826541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-101565765411349373989389676966060005000000000000)
      constant := (1327235898563001202868670963736550151325386266371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69924345987386223719/20000000000000000000)
  centralHi := (87405432484232779649/25000000000000000000)
  directionLo := (353171280126536806407/100000000000000000000)
  directionHi := (44146410015817100801/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree051.table
  base := (-121834257882524100823264564866086235057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-20696479944157040746473092909889861000000000000)
      constant := (275852502481990640444860426133261365871157283967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree051.table
  base := (-304647637473791740185778370680737796389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-51797532473221801564714178313655527500000000000)
      constant := (691135018296860681859702625411288279923480672459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353171280126536806407/100000000000000000000)
  centralHi := (44146410015817100801/12500000000000000000)
  directionLo := (44585688596570190943/12500000000000000000)
  directionHi := (71337101754512305509/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree052.table
  base := (7248402401480296514608791495948915197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-474792705602134647979018982000104972500000000000)
      constant := (6458883326787740058153891888069505156612166356948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree052.table
  base := (14470158908936754410029552062480067139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-52812182240768916134733518144281052500000000000)
      constant := (719217008888400735813199373160085041797644468582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44585688596570190943/12500000000000000000)
  centralHi := (71337101754512305509/20000000000000000000)
  directionLo := (11255170306285967889/3125000000000000000)
  directionHi := (360165449801150972449/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree053.table
  base := (47304928683344484340726972790733011361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-483914612460735879162393373527688072500000000000)
      constant := (6716158740381154558535559711038001301585148719048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree053.table
  base := (378393634376503566027489623600331827671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-53826832008316030704752857974906577500000000000)
      constant := (747863862468516892877642347417328101133660350599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11255170306285967889/3125000000000000000)
  centralHi := (360165449801150972449/100000000000000000000)
  directionLo := (363612087660173552287/100000000000000000000)
  directionHi := (11362877739380423509/3125000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree054.table
  base := (371864287676708866078068277370380906107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-54781835479926345593974196117252352500000000000)
      constant := (775389677661627309853306840700522339619246666966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree054.table
  base := (743689236389977735442143471082450040841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-54841481775863145274772197805532102500000000000)
      constant := (777075529646456240091066775066933345011464810329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363612087660173552287/100000000000000000000)
  centralHi := (11362877739380423509/3125000000000000000)
  directionLo := (73405272114396271157/20000000000000000000)
  directionHi := (183513180285990677893/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree055.table
  base := (1124841451830192467061806509821759246883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72117794178130523146674768556425000000000000)
      linear := (-4150069637834201169662331872585572500000000000)
      constant := (59883702686240045035777992443241058893863020483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree055.table
  base := (1124807670406680633644792087573954796479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-461620921846365783841252377158327500000000000)
      constant := (6668198089129371875098173762787670686394917031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73405272114396271157/20000000000000000000)
  centralHi := (183513180285990677893/50000000000000000000)
  directionLo := (370409163516291001823/100000000000000000000)
  directionHi := (11575286359884093807/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree056.table
  base := (608704614458060290366050800263307869991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (7862580)
      previous := (3931290)
      next := (3931290)
      square := (71234719147377904495899159145530000000000000)
      linear := (-4173717004379914879285849372330101000000000000)
      constant := (61374866941545137322264161041581209959621691839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree056.table
  base := (3043465073439923167296272553972099331769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-2321256380039076506726974590480945000000000000)
      constant := (34171148766599446492335774265935475270911001689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370409163516291001823/100000000000000000000)
  centralHi := (11575286359884093807/3125000000000000000)
  directionLo := (373761350970057817189/100000000000000000000)
  directionHi := (37376135097005781719/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree057.table
  base := (1934474896424017416704880427967251016401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (296450)
      previous := (148225)
      next := (148225)
      square := (2685827360896827731839842103825000000000000)
      linear := (-160173050137008557678021218725152500000000000)
      constant := (2399503341487590370540077830708972831276241529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree057.table
  base := (3868900020019575038015139540766688285637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-320694909022185534541995663697555000000000000)
      constant := (4809412897763252923893164167568040694845541773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373761350970057817189/100000000000000000000)
  centralHi := (37376135097005781719/10000000000000000000)
  directionLo := (377083739428110416417/100000000000000000000)
  directionHi := (188541869714055208209/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree058.table
  base := (2362969785412215431983699218036110894567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-529524146753742035079265331165603572500000000000)
      constant := (8078623267205615037511186386594014823753641277007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree058.table
  base := (4725896870461340057759603170650599817591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-117800161692103207109699114256068405000000000000)
      constant := (1799139187264596162007839539224698968680977431079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377083739428110416417/100000000000000000000)
  centralHi := (188541869714055208209/50000000000000000000)
  directionLo := (38037710972561349551/10000000000000000000)
  directionHi := (380377109725613495511/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree059.table
  base := (5614472595838019458601810620517049417223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1077292107224686532525279445386373345000000000000)
      constant := (16732663483339424795016208466612534838896829577583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree059.table
  base := (1403608993467136231187493356600006111551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-59914730613598718124868896958659727500000000000)
      constant := (931604820509694192916708934943135906961948604638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38037710972561349551/10000000000000000000)
  centralHi := (380377109725613495511/100000000000000000000)
  directionLo := (191821104590537523777/50000000000000000000)
  directionHi := (76728441836215009511/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree060.table
  base := (6534532163950316713639217320842389699491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-121726213437987666099114247604615505000000000000)
      constant := (1924247026444179712006792413232627904798709852179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree060.table
  base := (6534500764138391074185104730537817931287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-121858760762291665389776473578570505000000000000)
      constant := (1928409381899338096140822393318262048827770824903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191821104590537523777/50000000000000000000)
  centralHi := (76728441836215009511/20000000000000000000)
  directionLo := (96719938394140093063/25000000000000000000)
  directionHi := (386879753576560372253/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree061.table
  base := (935763023820425593958855636460700839153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-556889867329545728629388505748352872500000000000)
      constant := (8956962763534838533076489339768541071598294428452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree061.table
  base := (7486077275726983174538994274918931966429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-123888060297385894529815153239821555000000000000)
      constant := (1994738380013028071223210130416203064494053672301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96719938394140093063/25000000000000000000)
  centralHi := (386879753576560372253/100000000000000000000)
  directionLo := (78018085797995431921/20000000000000000000)
  directionHi := (195045214494988579803/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree062.table
  base := (8469176799696331809945693080491963804749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1132023548376293919625525794551871945000000000000)
      constant := (18519770121784770505600360975448792276691261311429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree062.table
  base := (169383074708526149022978556981426147719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428073800000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (38783347091350192447767319979233000000000000)
      linear := (-2518347196649602473397076658021452100000000000)
      constant := (41243932203228976956914400444562819802367168311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78018085797995431921/20000000000000000000)
  centralHi := (195045214494988579803/50000000000000000000)
  directionLo := (49159361686589759649/12500000000000000000)
  directionHi := (393274893492718077193/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree063.table
  base := (1185467497207999719770720456501018406657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-1304158006908726056680583421323172500000000000)
      constant := (21695869420913908446344905275196888940084737668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree063.table
  base := (4741860109110680742582705189106426264903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-1305578156811983191937678699615547500000000000)
      constant := (21742694398993938676491036671738362805677227943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49159361686589759649/12500000000000000000)
  centralHi := (393274893492718077193/100000000000000000000)
  directionLo := (79286755744911919571/20000000000000000000)
  directionHi := (12388555585142487433/3125000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree064.table
  base := (2105957056212019454011306565455404007471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-233702235162139768871804672132440869000000000000)
      constant := (3952377097361104261091295844366564974580600271191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree064.table
  base := (263244208929214993779214671882302355139/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-12997595890266858194993119222357470500000000000)
      constant := (220050068492455290898171747562407838438266025164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79286755744911919571/20000000000000000000)
  centralHi := (12388555585142487433/3125000000000000000)
  directionLo := (79913538271298541393/20000000000000000000)
  directionHi := (199783845678246353483/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree065.table
  base := (232146111810582832828844993657405969349/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (349050123822151732029905879813097000000000000)
      linear := (-23735099790558026134515442874347410900000000000)
      constant := (407963119146414051618415355046445066214885948029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree065.table
  base := (11607291098815818736436055657731969895351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-132005258437762811089969871884825755000000000000)
      constant := (2271346496533899164522185533442361693672942524519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79913538271298541393/20000000000000000000)
  centralHi := (199783845678246353483/50000000000000000000)
  directionLo := (50334651806385105503/12500000000000000000)
  directionHi := (16107088578043233761/4000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree066.table
  base := (1271629490314774214917045783994504586833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17689000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (1602617648402900514370550412365000000000000)
      linear := (-110651864393489785958909176012170500000000000)
      constant := (1932467229123541864158604788340476791636488937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree066.table
  base := (794767656063419518167466808986714579889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-553861809805194381115737816306102500000000000)
      constant := (9683146583481377078640244820793155453629252168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50334651806385105503/12500000000000000000)
  centralHi := (16107088578043233761/4000000000000000000)
  directionLo := (202881454364492176197/50000000000000000000)
  directionHi := (81152581745796870479/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree067.table
  base := (6928374078680572278525701219284444626287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-611621308481153115729634854913851472500000000000)
      constant := (10850560946403586137413980667585627192142891519127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree067.table
  base := (6928368769549743925673666574556844415563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-68031928753975634685023615603663927500000000000)
      constant := (1208212802100690352373331418710596838524894162747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202881454364492176197/50000000000000000000)
  centralHi := (81152581745796870479/20000000000000000000)
  directionLo := (81765062749888578703/20000000000000000000)
  directionHi := (102206328437360723379/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree068.table
  base := (15028661085370283044532610504178390972151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1241486430679508693826018492882869145000000000000)
      constant := (22367817178064123334941602638499799346560046773471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree068.table
  base := (15028651999350946194681594411196573781271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-138093157043045498510085910868578905000000000000)
      constant := (2490658880485963142946000503822456289427645228999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81765062749888578703/20000000000000000000)
  centralHi := (102206328437360723379/25000000000000000000)
  directionLo := (205932474505877020037/50000000000000000000)
  directionHi := (16474597960470161603/4000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree069.table
  base := (8116015044332526137870311545499341521563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-69985013577595064232931515329890852500000000000)
      constant := (1280258550644831600011077044442258015113166276747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree069.table
  base := (16232022315462941699409366308288905224047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-140122456578139727650124590529829955000000000000)
      constant := (2566021294431590925031694019198102860785488253343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205932474505877020037/50000000000000000000)
  centralHi := (16474597960470161603/4000000000000000000)
  directionLo := (207441157492057907353/50000000000000000000)
  directionHi := (414882314984115814707/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree070.table
  base := (4366713033268604532388573097621860321193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (178086797868444761239747897863825000000000000)
      linear := (-13040551613407281822035878152991852500000000000)
      constant := (242159510561096919096165349688055018652420565794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree070.table
  base := (4366711371100116693648710654440826538703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-1450528123604428130511870103990622500000000000)
      constant := (26964416730721030763687139825706271988074171486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207441157492057907353/50000000000000000000)
  centralHi := (414882314984115814707/100000000000000000000)
  directionLo := (417877894065603121493/100000000000000000000)
  directionHi := (208938947032801560747/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree071.table
  base := (18733124660273080690275352390983687553989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1296217871831116080926264842048367745000000000000)
      constant := (24428751498923869673918686409580026849116194937469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree071.table
  base := (4683279743651348518740806841493458443357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-72090527824164092965100974926166027500000000000)
      constant := (1360066755302352437453529542601237539309899157466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417877894065603121493/100000000000000000000)
  centralHi := (208938947032801560747/50000000000000000000)
  directionLo := (420852151486514036971/100000000000000000000)
  directionHi := (105213037871628509243/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree072.table
  base := (2503855689145532691827961868617698777449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-73025649197128807960722979172418552500000000000)
      constant := (1396445125659068663158295256907150661258358954724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree072.table
  base := (20030840651983729730898227842015017837681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-146210355183422415070240629513583105000000000000)
      constant := (2798883302845973877664135411234536101714219444289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420852151486514036971/100000000000000000000)
  centralHi := (105213037871628509243/25000000000000000000)
  directionLo := (52975692018980520961/12500000000000000000)
  directionHi := (423805536151844167689/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree073.table
  base := (267000160912035040676781469746373313783/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-133270549926552100565976240815870014500000000000)
      constant := (2585341428876975454302145741278001172833885226744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree073.table
  base := (21360008717511045931157481125679858397799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-148239654718516644210279309174834155000000000000)
      constant := (2878762212483891907582647675934237187839038647831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52975692018980520961/12500000000000000000)
  centralHi := (423805536151844167689/100000000000000000000)
  directionLo := (426738481432219126757/100000000000000000000)
  directionHi := (213369240716109563379/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree074.table
  base := (454412504122878813060532493151603720297/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (349050123822151732029905879813097000000000000)
      linear := (-27018986259654469360530223824277326900000000000)
      constant := (531619151002052913580373828762562219728875326337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree074.table
  base := (5680155413658086359150702552328613089183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-75134477126805436675158994418042602500000000000)
      constant := (1479885118136235830888429469258941580038163057054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426738481432219126757/100000000000000000000)
  centralHi := (213369240716109563379/50000000000000000000)
  directionLo := (1074128514765577187/250000000000000000)
  directionHi := (429651405906230874801/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree075.table
  base := (12056340609855389164536495257964162642253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-76066284816662551688514443014946252500000000000)
      constant := (1517702334497471949816941983876977121830436411357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree075.table
  base := (24112678184918889465136585818192825959011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-152298253788705102490356668497336255000000000000)
      constant := (3041907371475403899048469678312358060705062415059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1074128514765577187/250000000000000000)
  centralHi := (429651405906230874801/100000000000000000000)
  directionLo := (432544714057778190393/100000000000000000000)
  directionHi := (216272357028889095197/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree076.table
  base := (25536179823476076663853382574697029973027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5336100)
      previous := (2668050)
      next := (2668050)
      square := (48344892496142899173117157868850000000000000)
      linear := (-3843315624424178373296423150482545000000000000)
      constant := (77746447867935390718023683291136128216390693747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree076.table
  base := (25536177230685861338251959400518490251267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-427500147711355489280873540605505000000000000)
      constant := (8656990625446109268720556427672304128699762043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432544714057778190393/100000000000000000000)
  centralHi := (216272357028889095197/50000000000000000000)
  directionLo := (217709398465850247453/50000000000000000000)
  directionHi := (435418796931700494907/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree077.table
  base := (13495560049129240303904598813176659737257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16245000000000000000000000000000000000000000
      center := (162450)
      previous := (81225)
      next := (81225)
      square := (1471791717921031084626015684825000000000000)
      linear := (-118542819542446521768152938132852500000000000)
      constant := (2430800683969194049332843230829265967486347993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree077.table
  base := (26991117883478195325668910753286145574611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (36100)
      previous := (18050)
      next := (18050)
      square := (327064826204673574361336818850000000000000)
      linear := (-26371538684245835852662173691995000000000000)
      constant := (541333946240507208985285680247601298552434571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217709398465850247453/50000000000000000000)
  centralHi := (435418796931700494907/100000000000000000000)
  directionLo := (438274032750713816407/100000000000000000000)
  directionHi := (54784254093839227051/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree078.table
  base := (14238750634532893491651385781824647132707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-79106920436196295416305906857473952500000000000)
      constant := (1644030138698425137652434302978743008158784948883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree078.table
  base := (1139099975100136799646256483142175765463/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77566694182700384895534639958466000000000000)
      linear := (-6335446095759511596418908299243576200000000000)
      constant := (131803736970323632837995563718819398200948275847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438274032750713816407/100000000000000000000)
  centralHi := (54784254093839227051/12500000000000000000)
  directionLo := (13784712109262639669/3125000000000000000)
  directionHi := (441110787496404469409/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree079.table
  base := (29995322682483265127261270613245351530353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1442168381568735779860255106489697345000000000000)
      constant := (30370791625932586668580122092076475188287031082313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree079.table
  base := (3749415133404370160523717394584260309967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-80207725964541009525255693571170227500000000000)
      constant := (1690873492699375557431282100641893059621535031292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13784712109262639669/3125000000000000000)
  centralHi := (441110787496404469409/100000000000000000000)
  directionLo := (3551435323654456743/800000000000000000)
  directionHi := (110982353864201773219/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree080.table
  base := (15772291893803831409275188970348230017571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-730206097642969121113501944772431772500000000000)
      constant := (15579590943988639711009047808626560236610305813291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree080.table
  base := (15772291204265624475664235667609126073073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-81222375732088124095275033401795752500000000000)
      constant := (1734764824758642187614999051708258577563897183937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3551435323654456743/800000000000000000)
  centralHi := (110982353864201773219/25000000000000000000)
  directionLo := (446730259742886424119/100000000000000000000)
  directionHi := (11168256493572160603/2500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree081.table
  base := (33125284119970919968214122887927714480863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-164295112111460078288194741400003305000000000000)
      constant := (3550857030417614822479654512388247984315690258447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree081.table
  base := (4140660367839841682145818397833412726363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-82237025499635238665294373232421277500000000000)
      constant := (1779220707815979977753321631534278942554851391788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446730259742886424119/100000000000000000000)
  centralHi := (11168256493572160603/2500000000000000000)
  directionLo := (56189206597006786917/12500000000000000000)
  directionHi := (449513652776054295337/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree082.table
  base := (8684355821996197813156496286991797836031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-748449911360171583480250727827597972500000000000)
      constant := (16383192887866529269990370265006795322165141037902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree082.table
  base := (8684355570793388282541545864604787551141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-83251675267182353235313713063046802500000000000)
      constant := (1824241141457630063755226013331502036552096222058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56189206597006786917/12500000000000000000)
  centralHi := (449513652776054295337/100000000000000000000)
  directionLo := (452279916748682795337/100000000000000000000)
  directionHi := (226139958374341397669/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree083.table
  base := (1819050048075554389068266879279500923489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-151514363643754562932725023871036214500000000000)
      constant := (3358519938754129692805483900728404971017930093938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree083.table
  base := (36381000104009624820917421689544496515729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-168532650069458935610666105787344655000000000000)
      constant := (3739652250669668421337004950793110504462874364001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452279916748682795337/100000000000000000000)
  centralHi := (226139958374341397669/50000000000000000000)
  directionLo := (455029364059419548541/100000000000000000000)
  directionHi := (227514682029709774271/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree084.table
  base := (38056016862224230458603074679407778723283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-3477069047969950321301585083368545000000000000)
      constant := (78036630620911051233345442681415491182411724723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree084.table
  base := (9514004032635625160309461713601928534561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-1740428057189318007660252912740772500000000000)
      constant := (39101544064359783264737968653075856680636318082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455029364059419548541/100000000000000000000)
  centralHi := (227514682029709774271/50000000000000000000)
  directionLo := (28610143607810627387/6250000000000000000)
  directionHi := (457762297724970038193/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree085.table
  base := (39762470755485071268984513717298708516519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1551631263871950554060747804820694545000000000000)
      constant := (35253249920054559310145953993737384225039139299599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree085.table
  base := (39762470131250237921088771316114954384153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-172591249139647393890743465109846755000000000000)
      constant := (3925379485332488754421671922469283573800255172457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28610143607810627387/6250000000000000000)
  centralHi := (457762297724970038193/100000000000000000000)
  directionLo := (460479011769883431719/100000000000000000000)
  directionHi := (11511975294247085793/2500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree086.table
  base := (41500362443489007251344457366002736623737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1569875077589153016427496587875860745000000000000)
      constant := (36102486832429280514658204590724574822461502050577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree086.table
  base := (41500361910996286471437336556842952519657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-174620548674741623030782144771097805000000000000)
      constant := (4019936751327694181977507863843724498441545733433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460479011769883431719/100000000000000000000)
  centralHi := (11511975294247085793/2500000000000000000)
  directionLo := (92635958319152240241/20000000000000000000)
  directionHi := (231589895797880600603/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree087.table
  base := (43269691759488570412591616284871969941983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-176457654589595053199360596770114105000000000000)
      constant := (4106873870859314133950438747177002743432752211727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree087.table
  base := (43269691305316285527856331098188500732969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-176649848209835852170820824432348855000000000000)
      constant := (4115623115940860623226832445919938333125324125561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92635958319152240241/20000000000000000000)
  centralHi := (231589895797880600603/50000000000000000000)
  directionLo := (465864914331200856651/100000000000000000000)
  directionHi := (116466228582800214163/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree088.table
  base := (45070458562922008786872383412859833238281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144235588356261046293349537112850000000000000)
      linear := (-13275724834905437530256150032943745000000000000)
      constant := (312656065564136473011508820855520058311367573481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree088.table
  base := (45070458175601760564435631720205502306819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16026176484029005143705504123650000000000000)
      linear := (-1476687171445703151329417389203305000000000000)
      constant := (34813541974176155340141305323733655130305321291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465864914331200856651/100000000000000000000)
  centralHi := (116466228582800214163/25000000000000000000)
  directionLo := (234267324581844665729/50000000000000000000)
  directionHi := (468534649163689331459/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree089.table
  base := (2345133136765289643659819584804369782451/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-162460651874076040352774293704135934500000000000)
      constant := (3871104411672695233918351312903258777644107559542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree089.table
  base := (46902662405039926456580825975316585834309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-180708447280024310450898183754850955000000000000)
      constant := (4310383139881034236683961340623217580505594120021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234267324581844665729/50000000000000000000)
  centralHi := (468534649163689331459/100000000000000000000)
  directionLo := (471189257654571092177/100000000000000000000)
  directionHi := (235594628827285546089/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree090.table
  base := (12191576044192814535971238020873846923833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-91269462914331270327471762227584752500000000000)
      constant := (2200046965900519020960488787171514819733035028754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree090.table
  base := (24383151947595452250546808155388240377667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-91368873407559269795468431708051002500000000000)
      constant := (2204728399373660640033668399169801210168906739123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471189257654571092177/100000000000000000000)
  centralHi := (235594628827285546089/50000000000000000000)
  directionLo := (118457248509533524139/25000000000000000000)
  directionHi := (473828994038134096557/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree091.table
  base := (5066138280314437776927097464800422606981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35617359573688952247949579572765000000000000)
      linear := (-3389988053418704751553552047248350500000000000)
      constant := (82654668857318800102093740749552578339059833549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree091.table
  base := (50661382563102292556389034382628710212699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-3770756047963525892468888634231695000000000000)
      constant := (92033868475441370944649841636970224690800905019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118457248509533524139/25000000000000000000)
  centralHi := (473828994038134096557/100000000000000000000)
  directionLo := (59556763188222698359/12500000000000000000)
  directionHi := (476454105505781586873/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree092.table
  base := (1051757970869669957226256674328293310669/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (349050123822151732029905879813097000000000000)
      linear := (-33586759197847355812559785724137158900000000000)
      constant := (828217423539819790125573472538167990225569671749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree092.table
  base := (26293949169438367313460900258352368831379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-93398172942653498935507111369302052500000000000)
      constant := (2305495704689672895695324205764056456323249838851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59556763188222698359/12500000000000000000)
  centralHi := (476454105505781586873/100000000000000000000)
  directionLo := (59883104059523593127/12500000000000000000)
  directionHi := (479064832476188745017/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree093.table
  base := (6818231417250402778572231943495908601061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-94310098533865014055263226070112452500000000000)
      constant := (2351727538654000526005515283545203072586177326036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree093.table
  base := (27272925581810688840769182466268656875779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-94412822710200613505526451199927577500000000000)
      constant := (2356726180434712344213159110049624611348554222451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59883104059523593127/12500000000000000000)
  centralHi := (479064832476188745017/100000000000000000000)
  directionLo := (481661408852279882467/100000000000000000000)
  directionHi := (120415352213069970617/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree094.table
  base := (11307048227264778854063696477497671801733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-343165117465354543072297370463438069000000000000)
      constant := (8652292259091758487703553670598516164669431135293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree094.table
  base := (56535240987719266397462068940847491034927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-190854944955495456151091582061106205000000000000)
      constant := (4817042409660665274347595511742836648538935668063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481661408852279882467/100000000000000000000)
  centralHi := (120415352213069970617/25000000000000000000)
  directionLo := (484244062265803581181/100000000000000000000)
  directionHi := (242122031132901790591/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree095.table
  base := (11711213579199123714079573674296061625581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106722000000000000000000000000000000000000000
      center := (1067220)
      previous := (533610)
      next := (533610)
      square := (9668978499228579834623431573770000000000000)
      linear := (-960703269276440541677692872782469000000000000)
      constant := (24488624917026932108430294034708642144402627741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree095.table
  base := (58556067769372137138458726934828840244333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-534305386400525444019751417513455000000000000)
      constant := (13633688519843777954054452517578450193808650357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484244062265803581181/100000000000000000000)
  centralHi := (242122031132901790591/50000000000000000000)
  directionLo := (121703253577557395143/25000000000000000000)
  directionHi := (486813014310229580573/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree096.table
  base := (12121666316250754169738031492183575058869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-38940293661359503113221875965056061000000000000)
      constant := (1003391460764611646260967865722303962365176382661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree096.table
  base := (6060833147337200586911404416187785545153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-19491354402568391443116894138360830500000000000)
      constant := (502760979880288231204260810276286562359493581457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121703253577557395143/25000000000000000000)
  centralHi := (486813014310229580573/100000000000000000000)
  directionLo := (244684240381320903857/50000000000000000000)
  directionHi := (97873696152528361543/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree097.table
  base := (783650402024621195515605414701633596387/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-177055702847838010246173320148268894500000000000)
      constant := (4611340457240014935509797464844823816532697769816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree097.table
  base := (3918252004379102047599869825595104094441/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-98471421780389071785603810522429677500000000000)
      constant := (2567293569507515905478697426441560406344116709832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244684240381320903857/50000000000000000000)
  centralHi := (97873696152528361543/20000000000000000000)
  directionLo := (491910671795256399343/100000000000000000000)
  directionHi := (30744416987203524959/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree098.table
  base := (6480716961276598325810429419912097378143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35617359573688952247949579572765000000000000)
      linear := (-3650613963664454213935677519465010500000000000)
      constant := (96090478548413540993415451042933396930171979447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree098.table
  base := (64807169534481584451757721925864126481201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-4060655981548415769617271442981845000000000000)
      constant := (106993746454012331761220808595984005908825340881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491910671795256399343/100000000000000000000)
  centralHi := (30744416987203524959/6250000000000000000)
  directionLo := (494439792177151528969/100000000000000000000)
  directionHi := (49443979217715152897/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree099.table
  base := (66953743912270517190138353785576134460827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16026176484029005143705504123650000000000000)
      linear := (-1659361483850123991914812458763105000000000000)
      constant := (44137195117505310685037444326071826242477568803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree099.table
  base := (4184608990349648002938372632987238355773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-830584473681680172939194133749427500000000000)
      constant := (22115409547324782375507788942385150074202148776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494439792177151528969/100000000000000000000)
  centralHi := (49443979217715152897/10000000000000000000)
  directionLo := (496956041466757026223/100000000000000000000)
  directionHi := (31059752591672314139/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree100.table
  base := (13826351008497506031795824602714325727313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-365057693925997497912395910129637509000000000000)
      constant := (9811323510955087172214005176052364927783788786473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree100.table
  base := (2765270199428164720379049285727588529793/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77566694182700384895534639958466000000000000)
      linear := (-8121229686642433239652946401144500200000000000)
      constant := (218491749663805072127004872469881842933924513617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496956041466757026223/100000000000000000000)
  centralHi := (31059752591672314139/6250000000000000000)
  directionLo := (499459614195615883707/100000000000000000000)
  directionHi := (124864903548903970927/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree101.table
  base := (8917650373533414929508763933222850972551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-921766141673594975964364166851676872500000000000)
      constant := (25028985351933629537625779248501916706277648407484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree101.table
  base := (71341202939913695055834423099734926770389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-205060041701155060131362339689863555000000000000)
      constant := (5573787469642307286095851109855816350476610733541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499459614195615883707/100000000000000000000)
  centralHi := (124864903548903970927/25000000000000000000)
  directionLo := (501950700043896540247/100000000000000000000)
  directionHi := (62743837505487067531/12500000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree102.table
  base := (4598880483553696837777721334274465320141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-103432005392466245238637617597695552500000000000)
      constant := (2837192496110729525854143965056625154502438976232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree102.table
  base := (73582087695687903967819414810239504322843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-207089341236249289271401019351114605000000000000)
      constant := (5686410294567308840380941359877577302627979149067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501950700043896540247/100000000000000000000)
  centralHi := (62743837505487067531/12500000000000000000)
  directionLo := (252214742004052041517/50000000000000000000)
  directionHi := (100885896801620816607/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree103.table
  base := (15170881855506859100444464334112527763679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-376003982156318975332445179962737229000000000000)
      constant := (10418220046589276433256620347201084394433160717959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree103.table
  base := (75854409242481937931246833705676890562573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-209118640771343518411439699012365655000000000000)
      constant := (5800162216347561688414323568340765130576523809437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252214742004052041517/50000000000000000000)
  centralHi := (100885896801620816607/20000000000000000000)
  directionLo := (126724036640352505059/25000000000000000000)
  directionHi := (506896146561410020237/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree104.table
  base := (9769770950158528677144181483281301948697/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-949131862249398669514487341434426172500000000000)
      constant := (26561438306276584396112285904422707850942703370948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree104.table
  base := (78158167571428180889626741883567551995111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-211147940306437747551478378673616705000000000000)
      constant := (5915043234964085859684784423346987617696223735959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126724036640352505059/25000000000000000000)
  centralHi := (506896146561410020237/100000000000000000000)
  directionLo := (127337715951748463629/25000000000000000000)
  directionHi := (509350863806993854517/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree105.table
  base := (80493362700472670350023557906780592340067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-4345822082122448529242003324090745000000000000)
      constant := (122822662287227473592575097093269433054006466627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree105.table
  base := (80493362675072205566725871626402215147613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-4350555915133305646765654251731995000000000000)
      constant := (123082721436753594472194281671530350159862883453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127337715951748463629/25000000000000000000)
  centralHi := (509350863806993854517/100000000000000000000)
  directionLo := (255896903812382583873/50000000000000000000)
  directionHi := (511793807624765167747/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree106.table
  base := (82859994568769681631284272123735726090803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-1934751351933202263762472248979184745000000000000)
      constant := (55216852601165963111203058632441888030855213336763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree106.table
  base := (41429997273575121575987292256058459056761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-107603269688313102915777868998059402500000000000)
      constant := (3074096281322337860093609788797484565452860484809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255896903812382583873/50000000000000000000)
  centralHi := (511793807624765167747/100000000000000000000)
  directionLo := (514225145811812154509/100000000000000000000)
  directionHi := (51422514581181215451/10000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree107.table
  base := (21314515800200304593043807034610426997511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-976497582825202363064610516017175472500000000000)
      constant := (28139526104972948412116147011072806475400241188062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree107.table
  base := (85258063182401613195520430712017852363141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-217235838911720434971594417657369855000000000000)
      constant := (6266460871684074835480113512229541998644643739029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514225145811812154509/100000000000000000000)
  centralHi := (51422514581181215451/10000000000000000000)
  directionLo := (516645042216901376921/100000000000000000000)
  directionHi := (258322521108450688461/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree108.table
  base := (87687568592068565921233482658152114180827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-219026553263067465388441090565501905000000000000)
      constant := (6372376988324495200999421132332224822477102505163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree108.table
  base := (8768756857641062446882202155178921307123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-21926513844681466411163309731862090500000000000)
      constant := (638585827750967226639705970227324911619205548387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516645042216901376921/100000000000000000000)
  centralHi := (258322521108450688461/50000000000000000000)
  directionLo := (64881707108666728559/12500000000000000000)
  directionHi := (519053656869333828473/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree109.table
  base := (4507425536939849041693893366893888663371/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-198948279308480965086271859814468334500000000000)
      constant := (5843387465601692897082493438259055423521553030182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree109.table
  base := (45074255362736659645575539051399801256867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-110647218990954446625835888489935977500000000000)
      constant := (3253192390056770088370457721041947313716359163923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64881707108666728559/12500000000000000000)
  centralHi := (519053656869333828473/100000000000000000000)
  directionLo := (260725573051222036861/50000000000000000000)
  directionHi := (521451146102444073723/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree110.table
  base := (11580111204727697659124476053462535666087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72117794178130523146674768556425000000000000)
      linear := (-8296390937198397162105237112396072500000000000)
      constant := (245977262368489037913088253618456006562306865948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree110.table
  base := (92640889626485160291180560898007752219411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16026176484029005143705504123650000000000000)
      linear := (-1845650723281017540427359145794405000000000000)
      constant := (54777193218917633974898767334912784129009161179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260725573051222036861/50000000000000000000)
  centralHi := (521451146102444073723/100000000000000000000)
  directionLo := (65479707834001520957/12500000000000000000)
  directionHi := (523837662672012167657/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree111.table
  base := (47582352643245576840736180165349845097589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-112553912251067476422012009125278652500000000000)
      constant := (3368292300352313346868433452182578647601681470341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree111.table
  base := (9516470527684637100093184369903307184501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-22535303705209735153174913630237405500000000000)
      constant := (675082507563058838810357497433168944695183220869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65479707834001520957/12500000000000000000)
  centralHi := (523837662672012167657/100000000000000000000)
  directionLo := (32888334741865134771/6250000000000000000)
  directionHi := (526213355869842156337/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree112.table
  base := (9771995768258706528096925115855922398791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35617359573688952247949579572765000000000000)
      linear := (-4171865784155953138699928463898330500000000000)
      constant := (126004421215257285594751054480573098916714307039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree112.table
  base := (12214994709297769746043860253593540976209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19787421985382751248860877540425000000000000)
      linear := (-2320227924359097761957018530241072500000000000)
      constant := (70150396617689279057930697544715897853527141316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32888334741865134771/6250000000000000000)
  centralHi := (526213355869842156337/100000000000000000000)
  directionLo := (528578371632746130473/100000000000000000000)
  directionHi := (264289185816373065237/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree113.table
  base := (6269165426515932043621705420104399114581/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-1031229023976809750164856865182674072500000000000)
      constant := (31432606230270957150454016320246899304250316668008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree113.table
  base := (100306646817275477316210591190078137306963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-229411636122285809811826495624876155000000000000)
      constant := (6999781758194027445297194344629857967669567089347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528578371632746130473/100000000000000000000)
  centralHi := (264289185816373065237/50000000000000000000)
  directionLo := (530932852647158964483/100000000000000000000)
  directionHi := (132733213161789741121/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree114.table
  base := (20584954541989381730148856890267492033219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11858000000000000000000000000000000000000000
      center := (118580)
      previous := (59290)
      next := (59290)
      square := (1074330944358731092735936841530000000000000)
      linear := (-128082601518671712077344568385381000000000000)
      constant := (3939575229394235629352137515416679960264955451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree114.table
  base := (102924772704010375591442600965255398222963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5371654721793655463679684207650000000000000)
      linear := (-641110625089695398758629294421405000000000000)
      constant := (19739484057088027648717846081939494256063947627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530932852647158964483/100000000000000000000)
  centralHi := (132733213161789741121/25000000000000000000)
  directionLo := (266638469224797975547/50000000000000000000)
  directionHi := (106655387689919190219/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree115.table
  base := (105574335338373321987923327636937059685997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-2098945675388024425063211296475680545000000000000)
      constant := (65141727818353555930006511649984318087527519416037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree115.table
  base := (26393583833331061016455316577633996336731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-116735117596237134045951927473689127500000000000)
      constant := (3626627413887549253383014518288211398210505187478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266638469224797975547/50000000000000000000)
  centralHi := (106655387689919190219/20000000000000000000)
  directionLo := (26780538276157673373/5000000000000000000)
  directionHi := (535610765523153467461/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree116.table
  base := (2706383367711538764654801653315423300369/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-211718948910522688742996007953084674500000000000)
      constant := (6629519711105384681544488365891090625143549861796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree116.table
  base := (13531916838020948300996455333468887222631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-117749767363784248615971267304314652500000000000)
      constant := (3690842503845371356310282744454815439703261963356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26780538276157673373/5000000000000000000)
  centralHi := (535610765523153467461/100000000000000000000)
  directionLo := (537934467390241520437/100000000000000000000)
  directionHi := (268967233695120760219/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree117.table
  base := (110967770819321629401174180234208775180093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-237270366980269927755189873620668105000000000000)
      constant := (7495423053288120752534665519273745711923440474317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree117.table
  base := (110967770815670119470430360093153865750337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-237528834262662726371981214269880355000000000000)
      constant := (7511244284353847871680698766916654131482183054353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537934467390241520437/100000000000000000000)
  centralHi := (268967233695120760219/50000000000000000000)
  directionLo := (33765510918857903667/6250000000000000000)
  directionHi := (540248174701726458673/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree118.table
  base := (11371164367021716381319243439899606849591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1745250619110758660149529399065485000000000000)
      linear := (-215367711653963181216345764564117914500000000000)
      constant := (6863255892395709039616631418899077600517470151711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree118.table
  base := (113711643667112212249895394461217530804307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-239558133797756955512019893931131405000000000000)
      constant := (7641932657762873708055522320521962970190083769283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33765510918857903667/6250000000000000000)
  centralHi := (540248174701726458673/100000000000000000000)
  directionLo := (542552015322652254747/100000000000000000000)
  directionHi := (135638003830663063687/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree119.table
  base := (18201086446959505750194542884126261101/1562500000000000000000000000000000000)
  polynomial :=
    { denominator := 78625800000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (7123471914737790449589915914553000000000000)
      linear := (-886498338880340520216410787222998100000000000)
      constant := (28496510793524146425625933336073401531248003712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree119.table
  base := (116486953257900824301086178121164884588563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39574843970765502497721755080850000000000000)
      linear := (-4930355782303085401062419869232295000000000000)
      constant := (158647961794215324415514518906600633323713020403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542552015322652254747/100000000000000000000)
  centralHi := (135638003830663063687/25000000000000000000)
  directionLo := (544846114414699503099/100000000000000000000)
  directionHi := (5448461144146995031/1000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree120.table
  base := (119293699589793772030756516311120610705611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-243351638219337415210772801305723505000000000000)
      constant := (7890053893346075755299047139036064510415357910459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree120.table
  base := (119293699587549236581656470691015281997713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-243616732867945413792097253253633505000000000000)
      constant := (7906696694813837678244818504440918788114162976097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544846114414699503099/100000000000000000000)
  centralHi := (5448461144146995031/1000000000000000000)
  directionLo := (547130594515532604291/100000000000000000000)
  directionHi := (136782648628883151073/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree121.table
  base := (61065941328784073774687371975515991652703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72117794178130523146674768556425000000000000)
      linear := (-9125655197071236360593818160358172500000000000)
      constant := (298407684759879353535995757576455956387101970303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree121.table
  base := (61065941327829989363665380072610208445007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8013088242014502571852752061825000000000000)
      linear := (-1015066249599337367488165012044977500000000000)
      constant := (33226332059726790580426568351966179477183728823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547130594515532604291/100000000000000000000)
  centralHi := (136782648628883151073/25000000000000000000)
  directionLo := (274702787807588736039/50000000000000000000)
  directionHi := (549405575615177472079/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree122.table
  base := (31250375615883137433561216921534543840171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-1113326185704220830815226388930921972500000000000)
      constant := (36714487729728069944920678621678225931163573335782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree122.table
  base := (125001502461910450348489668534501877236639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-247675331938133872072174612576135605000000000000)
      constant := (8175977118835997339142115298266201883479107779791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274702787807588736039/50000000000000000000)
  centralHi := (549405575615177472079/100000000000000000000)
  directionLo := (68958896903695558603/12500000000000000000)
  directionHi := (22066847009182578753/4000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree123.table
  base := (31975639751854909298252083310604310791617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-124716454729202451333177864495389452500000000000)
      constant := (4147412904600307828723610344600583621169484973346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree123.table
  base := (12790255900604081283794473547089795267299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193916735456750962238836599896165000000000000)
      linear := (-24970463147322810121221329223738665500000000000)
      constant := (831231097595962358378164641793995692006473493331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68958896903695558603/12500000000000000000)
  centralHi := (22066847009182578753/4000000000000000000)
  directionLo := (553927508471364112121/100000000000000000000)
  directionHi := (276963754235682056061/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree124.table
  base := (130835052289015751824231994691077790780633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17452506191107586601495293990654850000000000000)
      linear := (-2263139998842846586363950343972176345000000000000)
      constant := (75888030181934890872669702961798349599778174062193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree124.table
  base := (65417526143921897345621467854085890916937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-125866965504161165176125985949318852500000000000)
      constant := (4224886964912159208439554141501908899255993529753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553927508471364112121/100000000000000000000)
  centralHi := (276963754235682056061/50000000000000000000)
  directionLo := (139043672029559092147/25000000000000000000)
  directionHi := (556174688118236368589/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree125.table
  base := (2675979646163043423197893320407691208397/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (349050123822151732029905879813097000000000000)
      linear := (-45627676251200980974613982540546850900000000000)
      constant := (1542655383136818792034282063587504381616229306437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree125.table
  base := (33449745576789027352516045178982755312431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-126881615271708279746145325779944377500000000000)
      constant := (4294182990214866172537689011945038594510625254078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139043672029559092147/25000000000000000000)
  centralHi := (556174688118236368589/100000000000000000000)
  directionLo := (139603206169652007537/25000000000000000000)
  directionHi := (558412824678608030149/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree126.table
  base := (13679434906469774410305897123016596416369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (436810)
      previous := (218405)
      next := (218405)
      square := (3957484397076550249772175508085000000000000)
      linear := (-521457511627494673718242156481294500000000000)
      constant := (17774977144562621473577863960261249948063414289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree126.table
  base := (6839717453192561616270508063000333471201/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (436810)
      previous := (218405)
      next := (218405)
      square := (3957484397076550249772175508085000000000000)
      linear := (-522025571588797527821080267798244500000000000)
      constant := (17812422709746111344675911017268379632711061762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139603206169652007537/25000000000000000000)
  centralHi := (558412824678608030149/100000000000000000000)
  directionLo := (560642026455086725783/100000000000000000000)
  directionHi := (70080253306885840723/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree127.table
  base := (69910576279276346318862524145129821840851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8726253095553793300747646995327425000000000000)
      linear := (-1158935719997226986732098346568837472500000000000)
      constant := (39826335166986816053505792569843149989793123726171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree127.table
  base := (27964230511566664504457475641022778102207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387833470913501924477673199792330000000000000)
      linear := (-51564365922721003554473602176478171000000000000)
      constant := (1773787474372339984680635937193482764543842694383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560642026455086725783/100000000000000000000)
  centralHi := (70080253306885840723/12500000000000000000)
  directionLo := (562862399605614532597/100000000000000000000)
  directionHi := (281431199802807266299/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree128.table
  base := (28575878557928679241078775968805372733577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3490501238221517320299058798130970000000000000)
      linear := (-467223050742331287166189095238568229000000000000)
      constant := (16185566507239387130172630510930455753491541229217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree128.table
  base := (71439696394516054818240389463592251156901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-129925564574349623456203345271820952500000000000)
      constant := (4505458356343949017051071639218938203016445036469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell112.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562862399605614532597/100000000000000000000)
  centralHi := (281431199802807266299/50000000000000000000)
  directionLo := (565074048202458890251/100000000000000000000)
  directionHi := (141268512050614722563/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree129.table
  base := (145969069757918004209276237410784042116031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1939167354567509622388365998961650000000000000)
      linear := (-261595451936539877577521584360889705000000000000)
      constant := (9134792868243341390593676648009366499439847155439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree129.table
  base := (72984534878699296804466621912546130473371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (969583677283754811194182999480825000000000000)
      linear := (-130940214341896738026222685102446477500000000000)
      constant := (4577012575127042006390341573924675396235158613899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell112.Kernel129
