import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell007.Parameters
import ForestUnimodality.BinomialMassData.Q19_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q13_42.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_42.Batch050_099
import ForestUnimodality.BinomialMassData.Q13_42.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree000.table
  base := (1534789808127014700265267061/250000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (1009598084316112802383269558000000000000)
      constant := (193383515824003852233423649686000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree000.table
  base := (1534789808127014700265267061/250000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (673065389544075201588846372000000000000)
      constant := (128922343882669234822282433124000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree001.table
  base := (8655918126416436079965370859620474930713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (2573399227179298573431331956000000000000)
      constant := (544325825775946336165784048334089920634919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree001.table
  base := (21404315479536021074808731015717853993449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (2112372314094916516541422545000000000000)
      constant := (448642885898785028251717714338824933862429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29217477094198368143/100000000000000000000)
  directionHi := (1826092318387398009/6250000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree002.table
  base := (15209894613860996603749296698727090419501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (2771015292735364843323964200000000000000)
      constant := (954342838029083526282618762879806696428563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree002.table
  base := (14879070646434966510312301643633329396573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (859417680469457025138613230000000000000)
      constant := (311152824523551729349175549131299917328033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29217477094198368143/100000000000000000000)
  centralHi := (1826092318387398009/6250000000000000000)
  directionLo := (41319752364940579789/100000000000000000000)
  directionHi := (4131975236494057979/10000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree003.table
  base := (21255604200394383637024922914080975298893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-1782934964955033493860802980000000000000)
      constant := (1330775171584227663691563306077101443830259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree003.table
  base := (10278661694133641619155389430003350658451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-393536953156002466264196085000000000000)
      constant := (214472135936473014857911732848820363827471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41319752364940579789/100000000000000000000)
  centralHi := (4131975236494057979/10000000000000000000)
  directionLo := (25303077398065728927/50000000000000000000)
  directionHi := (10121230959226291571/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree004.table
  base := (14693323208201779755377613874864720068793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-9107900515380796674369534360000000000000)
      constant := (918993737918366482427119157316477364333959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree004.table
  base := (1754622769204416121337041691062852908077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-1646491586781461957667005400000000000000)
      constant := (146324271675446864542139885669279644278468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25303077398065728927/50000000000000000000)
  centralHi := (10121230959226291571/20000000000000000000)
  directionLo := (58434954188396736287/100000000000000000000)
  directionHi := (1826092318387398009/3125000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree005.table
  base := (4982114696135219020166361295587707273339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-8216433032903279927439132870000000000000)
      constant := (312456106475768833435898313547025558220357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree005.table
  base := (9384496223981897696575507507872997828521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-5798892440813842898139629430000000000000)
      constant := (196353414816110933858399059702832954398941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58434954188396736287/100000000000000000000)
  centralHi := (1826092318387398009/3125000000000000000)
  directionLo := (32666132456835288749/50000000000000000000)
  directionHi := (65332264913670577499/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree006.table
  base := (6565229260287452317935255897788053698037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-23757831616232323035386997120000000000000)
      constant := (416835706668028128066431146000647382976331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree006.table
  base := (1214448042551693634823697704677540640031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-1660960341612952376189049612000000000000)
      constant := (25795750630215739591951054604228353440651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32666132456835288749/50000000000000000000)
  centralHi := (65332264913670577499/100000000000000000000)
  directionLo := (35783955226120679313/50000000000000000000)
  directionHi := (71567910452241358627/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree007.table
  base := (255251897502340528915521028482301258847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-7770699291664521553973932125000000000000)
      constant := (67197448644567324025549860420039917229444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree007.table
  base := (1837526911075493657409060908283132113669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-5405355487657840431875433345000000000000)
      constant := (40798096050850953264849080682695774387049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35783955226120679313/50000000000000000000)
  centralHi := (71567910452241358627/100000000000000000000)
  directionLo := (77302178327974977109/100000000000000000000)
  directionHi := (7730217832797497711/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree008.table
  base := (2816733036908606655091692382890053083/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-1920388135854192469820222994000000000000)
      constant := (8196898108833403925199453076882933769160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree008.table
  base := (1919671105396632542717325785333938781273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-13316620242566599846556485320000000000000)
      constant := (48467146785961285473129011092012714406733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77302178327974977109/100000000000000000000)
  centralHi := (7730217832797497711/10000000000000000000)
  directionLo := (82639504729881159579/100000000000000000000)
  directionHi := (4131975236494057979/5000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree009.table
  base := (885072364307417061994031705033493356601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-45732728267509612576913191260000000000000)
      constant := (90422027882978687338174583267110081465863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree009.table
  base := (615727115791666156277879352652557531109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-15822529509817518829362103950000000000000)
      constant := (25593953323078343057745179583203708153289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82639504729881159579/100000000000000000000)
  centralHi := (4131975236494057979/5000000000000000000)
  directionLo := (87652431282595104431/100000000000000000000)
  directionHi := (5478276955162194027/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree010.table
  base := (-153662111454978589882407027784957714993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-53057693817935375757421922640000000000000)
      constant := (39878724319657719828311063449547663955441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree010.table
  base := (-73917316779374509086333983736098394659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-3665687755413687562433544516000000000000)
      constant := (2037526906232180912797233131541933712161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87652431282595104431/100000000000000000000)
  centralHi := (5478276955162194027/6250000000000000000)
  directionLo := (18478755020292966893/20000000000000000000)
  directionHi := (46196887550732417233/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree011.table
  base := (-95652952699436407213922799671558682379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-6038265936836113893793065402000000000000)
      constant := (640416214495924221765276269691803010123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree011.table
  base := (-1129023575242987105952638464756318537861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-20834348044319356794973341210000000000000)
      constant := (300365197154895577484324157617310704919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18478755020292966893/20000000000000000000)
  centralHi := (46196887550732417233/50000000000000000000)
  directionLo := (48451704421129679957/50000000000000000000)
  directionHi := (19380681768451871983/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree012.table
  base := (-198720913023697960075288560952584814897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-16926906229696725529609846350000000000000)
      constant := (-3543654054870984032707647000025686677022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree012.table
  base := (-107965979339731439266312071543186560249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-11670128655785137888889479920000000000000)
      constant := (-2715081356954609732127824479255342121832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48451704421129679957/50000000000000000000)
  centralHi := (19380681768451871983/20000000000000000000)
  directionLo := (101212309592262915709/100000000000000000000)
  directionHi := (10121230959226291571/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree013.table
  base := (-262533379965287519649053826607700306289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-18758147617303166324737029195000000000000)
      constant := (-6202945341154141989537065430070238592414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree013.table
  base := (-276291997925066099683867836380584552223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-12923083289410597380292289235000000000000)
      constant := (-3979232328733559374316068537219102386732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101212309592262915709/100000000000000000000)
  centralHi := (10121230959226291571/10000000000000000000)
  directionLo := (105345111802826817907/100000000000000000000)
  directionHi := (26336277950706704477/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree014.table
  base := (-2521289453028175813329078244279866326431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-82357556019638428479456848160000000000000)
      constant := (-27602758614885378883727742389631578565153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree014.table
  base := (-2609582654540356527185523722330748450667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-28352075846072113743390197100000000000000)
      constant := (-7954821518979536661308909178945717464007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105345111802826817907/100000000000000000000)
  centralHi := (26336277950706704477/25000000000000000000)
  directionLo := (5466089449620287831/5000000000000000000)
  directionHi := (109321788992405756621/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree015.table
  base := (-23011861370789755938222063263215424259/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-17936504314012838331993115908000000000000)
      constant := (-4807475997301085206659188229564293207925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree015.table
  base := (-2947670247565820760557463751123842619759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-30857985113323032726195815730000000000000)
      constant := (-5891199157369798608493243036100695014939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5466089449620287831/5000000000000000000)
  centralHi := (109321788992405756621/100000000000000000000)
  directionLo := (113158802204026951133/100000000000000000000)
  directionHi := (56579401102013475567/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree016.table
  base := (-3182708463230812112567257898583607097511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-97007487120489954840474310920000000000000)
      constant := (-15177936897930207274166520570767247143193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree016.table
  base := (-3240475952308917394671275965121953506363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-33363894380573951709001434360000000000000)
      constant := (-2101018559109818428959915587561023633623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113158802204026951133/100000000000000000000)
  centralHi := (56579401102013475567/50000000000000000000)
  directionLo := (4674796335071738903/4000000000000000000)
  directionHi := (1826092318387398009/1562500000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree017.table
  base := (-3452030966924515369834870938432372195559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-104332452670915718020983042300000000000000)
      constant := (-1784470058913609431488922151239448320217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree017.table
  base := (-874815159631603772716293180899894507243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-17934901823912435345903526495000000000000)
      constant := (1589621005454130994594306810954430695794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4674796335071738903/4000000000000000000)
  centralHi := (1826092318387398009/1562500000000000000)
  directionLo := (60233372086722214763/50000000000000000000)
  directionHi := (120466744173444429527/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree018.table
  base := (-923279235259145927707699083050137665759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-27914354555335370300372943420000000000000)
      constant := (3899253684579709337368574477841327057183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree018.table
  base := (-3732048727663017282496637477523135154143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-38375712915075789674612671620000000000000)
      constant := (9781069702345670545445192122014161762997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60233372086722214763/50000000000000000000)
  centralHi := (120466744173444429527/100000000000000000000)
  directionLo := (15494907136852717421/12500000000000000000)
  directionHi := (123959257094821739369/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree019.table
  base := (-782444485565391204946319859459427401351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-23796476754353448876400101012000000000000)
      constant := (7314477366278196610119906184056073714887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree019.table
  base := (-3944590190081463708529066986648291945279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-40881622182326708657418290250000000000000)
      constant := (17583715137584872721578487957885869149141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15494907136852717421/12500000000000000000)
  centralHi := (123959257094821739369/100000000000000000000)
  directionLo := (63678015019412547731/50000000000000000000)
  directionHi := (127356030038825095463/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree020.table
  base := (-1028472163126856656223188906335894310033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-31576837330548251890627309110000000000000)
      constant := (15213887257989946482622950500838658467921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree020.table
  base := (-828206394315574034880454570030462919323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-8677506289915525528044781776000000000000)
      constant := (5300018490981487320670491509360278694217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63678015019412547731/50000000000000000000)
  centralHi := (127356030038825095463/100000000000000000000)
  directionLo := (130664529827341154997/100000000000000000000)
  directionHi := (65332264913670577499/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree021.table
  base := (-1075358355554738944186737458078591869863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-33408078718154692685754491955000000000000)
      constant := (22059369872536187316722996663548712198631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree021.table
  base := (-540548408649635683380460121414315382517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-22946720358414273311514763755000000000000)
      constant := (18233462258185768832645578459947507868572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130664529827341154997/100000000000000000000)
  centralHi := (65332264913670577499/50000000000000000000)
  directionLo := (16736412549975302971/12500000000000000000)
  directionHi := (133891300399802423769/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree022.table
  base := (-4477298619692738642067763395676179472809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-140957280423044533923526699200000000000000)
      constant := (118564339593880577868064451792400693213033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree022.table
  base := (-4496864080911617142620143654679396904221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-48399349984079465605835146140000000000000)
      constant := (47437843364554517227890687681732665011359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16736412549975302971/12500000000000000000)
  centralHi := (133891300399802423769/100000000000000000000)
  directionLo := (137042115024908087563/100000000000000000000)
  directionHi := (34260528756227021891/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree023.table
  base := (-2321648182407845949181879477500654685603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-74141122986735148552017715290000000000000)
      constant := (75860982895145760525484875562458754807011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree023.table
  base := (-2330047855764539208848177145947554590371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-25452629625665192294320382385000000000000)
      constant := (29689274799248248871646244303851353602209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137042115024908087563/100000000000000000000)
  centralHi := (34260528756227021891/25000000000000000000)
  directionLo := (70061048840011925201/50000000000000000000)
  directionHi := (140122097680023850403/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree024.table
  base := (-2400391881925288108977766092498599900321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-77803605761948030142272080980000000000000)
      constant := (93812430192411828229705178572588206279777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree024.table
  base := (-300956431501931378079395076987062922711/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-26705584259290651785723191700000000000000)
      constant := (36131703807793695657269192186173428984552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70061048840011925201/50000000000000000000)
  centralHi := (140122097680023850403/100000000000000000000)
  directionLo := (35783955226120679313/25000000000000000000)
  directionHi := (143135820904482717253/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree025.table
  base := (-2475393640505637488977397495306823715651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-81466088537160911732526446670000000000000)
      constant := (113104178066001165667674209920670105913987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree025.table
  base := (-4963408229052443189394404232310058683769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-55917077785832222554252002030000000000000)
      constant := (86073043432484739748528820058988767640851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35783955226120679313/25000000000000000000)
  centralHi := (143135820904482717253/100000000000000000000)
  directionLo := (146087385470991840719/100000000000000000000)
  directionHi := (1826092318387398009/1250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree026.table
  base := (-2547045763659131629696671507311088216787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-85128571312373793322780812360000000000000)
      constant := (133711511268768807786890406859401442342419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree026.table
  base := (-5105117089042002227627813214445396332281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-58422987053083141537057620660000000000000)
      constant := (100792643597774234864520387326646677022099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146087385470991840719/100000000000000000000)
  centralHi := (1826092318387398009/1250000000000000000)
  directionLo := (148980485841267695451/100000000000000000000)
  directionHi := (37245121460316923863/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree027.table
  base := (-1046260575756932353793358403652998018803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-35516421635034669965214071220000000000000)
      constant := (62246131582520580930576749163861124815411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree027.table
  base := (-1310243833391108639563801272306416583123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-30464448160167030259931619645000000000000)
      constant := (58205372635296956691267645521880503508834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148980485841267695451/100000000000000000000)
  centralHi := (37245121460316923863/25000000000000000000)
  directionLo := (151818464388394373563/100000000000000000000)
  directionHi := (37954616097098593391/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree028.table
  base := (-2681447628330369763262923253847456429477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-92453536862799556503289543740000000000000)
      constant := (178800702609215625161031416127610244942949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree028.table
  base := (-5371410452328565335411102570997563978137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-63434805587584979502668857920000000000000)
      constant := (132918371167058447065748554209051156459123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151818464388394373563/100000000000000000000)
  centralHi := (37954616097098593391/25000000000000000000)
  directionLo := (77302178327974977109/50000000000000000000)
  directionHi := (154604356655949954219/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree029.table
  base := (-5489243238318068299675567621908973756583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-192232039276024876187087818860000000000000)
      constant := (406511666080613631222199221269734653335271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree029.table
  base := (-549676120617529711521346197748725774669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-6594071485483589848547447655000000000000)
      constant := (15030840730950888223568309415026758731951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77302178327974977109/50000000000000000000)
  centralHi := (154604356655949954219/100000000000000000000)
  directionLo := (157340929400935544457/100000000000000000000)
  directionHi := (78670464700467772229/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree030.table
  base := (-5610646145796607562242560752181815829427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-199557004826450639367596550240000000000000)
      constant := (457942583210632600502216773212545602746099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree030.table
  base := (-1123459818247773829528403715950488574249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-13689324824417363493656019036000000000000)
      constant := (33715030455825238928552894035039739940771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157340929400935544457/100000000000000000000)
  centralHi := (78670464700467772229/50000000000000000000)
  directionLo := (20003839097353674267/12500000000000000000)
  directionHi := (160030712778829394137/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree031.table
  base := (-572734568874546253970697190694447499029/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-20688197037687640254810528162000000000000)
      constant := (51187892890059452895686628955249807561173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree031.table
  base := (-5733244011900905565643941750983582048489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-70952533389337736451085713810000000000000)
      constant := (187713988083896277495102125446844776981731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20003839097353674267/12500000000000000000)
  centralHi := (160030712778829394137/100000000000000000000)
  directionLo := (81338013868440068803/50000000000000000000)
  directionHi := (162676027736880137607/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree032.table
  base := (-14598847462921345309779182364374457901/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-10710346796365108286430700650000000000000)
      constant := (28415414235812670420002342156888183044740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree032.table
  base := (-2922387914012750708006151323875311945601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-36729221328294327716945666220000000000000)
      constant := (103860568833336567405020782838618449142379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81338013868440068803/50000000000000000000)
  centralHi := (162676027736880137607/100000000000000000000)
  directionLo := (82639504729881159579/50000000000000000000)
  directionHi := (165279009459762319159/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree033.table
  base := (-47579106022169730533950144273303968241/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-44306380295545585781824548876000000000000)
      constant := (125444086188434034542574174307546250020425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree033.table
  base := (-2976021473451420799442379767028310695597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-37982175961919787208348475535000000000000)
      constant := (114296742237181441842345983661155475392463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82639504729881159579/50000000000000000000)
  centralHi := (165279009459762319159/100000000000000000000)
  directionLo := (83920813770706204499/50000000000000000000)
  directionHi := (167841627541412408999/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree034.table
  base := (-6051028089613326832046687497630967772849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-228856867028153692089631475760000000000000)
      constant := (688606887900575549923202264249249030310513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree034.table
  base := (-6055168784803058590540305390581402352217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-78470261191090493399502569700000000000000)
      constant := (250328436765292742117194477787790550603443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83920813770706204499/50000000000000000000)
  centralHi := (167841627541412408999/100000000000000000000)
  directionLo := (34073140685003027657/20000000000000000000)
  directionHi := (85182851712507569143/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree035.table
  base := (-6150570998739554637348688882419222439109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-236181832578579455270140207140000000000000)
      constant := (752460567899654387076760795857588986336133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree035.table
  base := (-3077128340770619823165990744879380253081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-40488085229170706191154094165000000000000)
      constant := (136461912201672938872567615176283014685299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34073140685003027657/20000000000000000000)
  centralHi := (85182851712507569143/50000000000000000000)
  directionLo := (172852925550163081809/100000000000000000000)
  directionHi := (17285292555016308181/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree036.table
  base := (-1561527906212159605424042349244782444671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-60876699532251304612662234630000000000000)
      constant := (204693877080846536690905860557578705985727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree036.table
  base := (-31246968411838325682419295442610540619/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-8348207972559233136511380696000000000000)
      constant := (29637781943826640279380872862103572940020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172852925550163081809/100000000000000000000)
  centralHi := (17285292555016308181/10000000000000000000)
  directionLo := (87652431282595104431/50000000000000000000)
  directionHi := (175304862565190208863/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree037.table
  base := (-198054063717358953540346969823275997407/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-62707940919857745407789417475000000000000)
      constant := (221886666174457901076766460451568897306872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree037.table
  base := (-1585163370715252396433886875966694459393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-42993994496421625173959712795000000000000)
      constant := (160344437131451076121841588468148832705494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87652431282595104431/50000000000000000000)
  centralHi := (175304862565190208863/100000000000000000000)
  directionLo := (22215371862304542633/12500000000000000000)
  directionHi := (35544594979687268213/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree038.table
  base := (-6425494313290220093160592180239413426783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-258156729229856744811666401280000000000000)
      constant := (958769748472493125302380544284916954112671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree038.table
  base := (-1285619749810054153855262615013815958753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-17698779652018833866145008844000000000000)
      constant := (69171134578128834563156796434709864866187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22215371862304542633/12500000000000000000)
  centralHi := (35544594979687268213/20000000000000000000)
  directionLo := (180108624930901740791/100000000000000000000)
  directionHi := (22513578116362717599/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree039.table
  base := (-3254731281022472678263663095920334132411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-132740847390141253996087566330000000000000)
      constant := (516220549226634009725269060082018949658107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree039.table
  base := (-6511782966107647217273025693615725416731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-90999807527345088313530662850000000000000)
      constant := (371877092132876295376606876611569766248649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180108624930901740791/100000000000000000000)
  centralHi := (22513578116362717599/12500000000000000000)
  directionLo := (91231542985759928463/50000000000000000000)
  directionHi := (182463085971519856927/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree040.table
  base := (-263587383042497994849926477799832134919/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-54561332066141654234536772808000000000000)
      constant := (221711515563412133995311317253052877500515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree040.table
  base := (-6591751927252848346482936675994297878101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-93505716794596007296336281480000000000000)
      constant := (398752170331984622174249582604119744559879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91231542985759928463/50000000000000000000)
  centralHi := (182463085971519856927/100000000000000000000)
  directionLo := (184787550202929668931/100000000000000000000)
  directionHi := (46196887550732417233/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree041.table
  base := (-666620314556027370351819984480219735577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-28013162588113403435319259542000000000000)
      constant := (118711649078016605271014461706746156658649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree041.table
  base := (-266721797793841609227971327991337966957/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-19202325212369385255828380022000000000000)
      constant := (85296016385681133131810823884409513469515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184787550202929668931/100000000000000000000)
  centralHi := (46196887550732417233/25000000000000000000)
  directionLo := (18708313573850064973/10000000000000000000)
  directionHi := (187083135738500649731/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree042.table
  base := (-84238189256943188494476564289412083729/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-14372829571577989876685066340000000000000)
      constant := (63405775726575537969969952085068154900292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree042.table
  base := (-1685173961109309594032532326097412785821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-49258767664548922630973759370000000000000)
      constant := (227530058292794550100325571118908662995518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18708313573850064973/10000000000000000000)
  centralHi := (187083135738500649731/100000000000000000000)
  directionLo := (18935089290917079107/10000000000000000000)
  directionHi := (189350892909170791071/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree043.table
  base := (-3404136200510537016325237100400753345381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-147390778490992780357105029090000000000000)
      constant := (675776321576395373973760034719752539240997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree043.table
  base := (-6809733787283506129716975657225981025919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-101023444596348764244753137370000000000000)
      constant := (484491661917136595513269137035754398455701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18935089290917079107/10000000000000000000)
  centralHi := (189350892909170791071/100000000000000000000)
  directionLo := (95795904940203826653/50000000000000000000)
  directionHi := (191591809880407653307/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree044.table
  base := (-6873882476005569827189997620338722071687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-302106522532411323894718789560000000000000)
      constant := (1437426141053954344697638412318660509483719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree044.table
  base := (-6875183955794531772520252721395217835219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-103529353863599683227558756000000000000000)
      constant := (514774189092444697694639064090700425460401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95795904940203826653/50000000000000000000)
  centralHi := (191591809880407653307/100000000000000000000)
  directionLo := (48451704421129679957/25000000000000000000)
  directionHi := (193806817684518719829/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree045.table
  base := (-433494327599718300139233848749528941323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-77357872020709271768806880235000000000000)
      constant := (381433626010387219572384540277618706786604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree045.table
  base := (-867133516037412906827653481648073851063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-53017631565425301105182187315000000000000)
      constant := (272953620383302329896527154460311796510708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48451704421129679957/25000000000000000000)
  centralHi := (193806817684518719829/100000000000000000000)
  directionLo := (12249799671313233281/6250000000000000000)
  directionHi := (195996794741011732497/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree046.table
  base := (-279774936828912743089376991201374714711/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-63351290726652570051147250464000000000000)
      constant := (323295285314171976939312807539566964866035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree046.table
  base := (-6995405163584289727161736070310425101773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-108541172398101521193169993260000000000000)
      constant := (577890420905100629634536336153481072862767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12249799671313233281/6250000000000000000)
  centralHi := (195996794741011732497/100000000000000000000)
  directionLo := (39632514185451465319/20000000000000000000)
  directionHi := (49540642731814331649/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree047.table
  base := (-110145203479928951064004433568069324989/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-81020354795922153359061245925000000000000)
      constant := (427412693513557325954470785205886120411088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree047.table
  base := (-3525105705617052802345468476028550940397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-55523540832676220087987805945000000000000)
      constant := (305361693083327852256776397312150430251663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39632514185451465319/20000000000000000000)
  centralHi := (49540642731814331649/25000000000000000000)
  directionLo := (200304931252953173411/100000000000000000000)
  directionHi := (50076232813238293353/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree048.table
  base := (-7100683716671422725204687974239174704683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-331406384734114376616753715080000000000000)
      constant := (1805256559338481431478839192662931993604971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree048.table
  base := (-7101501060484209281201042630457774939769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-113552990932603359158781230520000000000000)
      constant := (644405838577325258156267229560386726264851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200304931252953173411/100000000000000000000)
  centralHi := (50076232813238293353/25000000000000000000)
  directionLo := (101212309592262915709/50000000000000000000)
  directionHi := (202424619184525831419/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree049.table
  base := (-714855914985269814279019761140949211667/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-33873135028454013979726244646000000000000)
      constant := (190329292264611215804290690353120199664979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree049.table
  base := (-7149286437771200251110664250647184825017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-116058900199854278141586849150000000000000)
      constant := (678937519281940701179888806913909118674643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101212309592262915709/50000000000000000000)
  centralHi := (202424619184525831419/100000000000000000000)
  directionLo := (102261169829694288503/50000000000000000000)
  directionHi := (204522339659388577007/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree050.table
  base := (-7192931220093066973948423689766089094409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-346056315834965902977771177840000000000000)
      constant := (2003759114413592848765062778544736387052233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree050.table
  base := (-7193578261226191942935980983571858299311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-118564809467105197124392467780000000000000)
      constant := (714318203199748651585577764094990975714469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102261169829694288503/50000000000000000000)
  centralHi := (204522339659388577007/100000000000000000000)
  directionLo := (206598761824702898947/100000000000000000000)
  directionHi := (51649690456175724737/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree051.table
  base := (-3616905154758187760580931035476582617/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-17669064069269583307913995461000000000000)
      constant := (105332724028356059329445478920997529512900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree051.table
  base := (-3617192929424053242572656035543085254609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-60535359367178058053599043205000000000000)
      constant := (375273847221385872337749698512345209653211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206598761824702898947/100000000000000000000)
  centralHi := (51649690456175724737/25000000000000000000)
  directionLo := (41730904306161553503/20000000000000000000)
  directionHi := (52163630382701941879/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree052.table
  base := (-227225171423044173235706406485147733659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-90176561733954357334697160150000000000000)
      constant := (552994612464891354172596372811485542235864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree052.table
  base := (-7271717355907099040782159275297634534649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-123576628001607035090003705040000000000000)
      constant := (787625822380336722025740168698749674772371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41730904306161553503/20000000000000000000)
  centralHi := (52163630382701941879/25000000000000000000)
  directionLo := (42138044721130727163/20000000000000000000)
  directionHi := (26336277950706704477/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree053.table
  base := (-1826281168518541567649160716199956014873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-92007803121560798129824342995000000000000)
      constant := (579932630739523117402653281001902771063001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree053.table
  base := (-456598739761534444139415853868564224219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-63041268634428977036404661835000000000000)
      constant := (412776219126517286106116663368831210331208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42138044721130727163/20000000000000000000)
  centralHi := (26336277950706704477/12500000000000000000)
  directionLo := (212706443933300560611/100000000000000000000)
  directionHi := (53176610983325140153/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree054.table
  base := (-733557480906894057341589664863138683049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-37535617803666895569980610336000000000000)
      constant := (242991026302433701247080145333622262967913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree054.table
  base := (-1833994870224387246049941345359678529077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-64294223268054436527807471150000000000000)
      constant := (432163706127653241439045248989893501778766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212706443933300560611/100000000000000000000)
  centralHi := (53176610983325140153/25000000000000000000)
  directionLo := (107351865678362037939/50000000000000000000)
  directionHi := (214703731356724075879/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree055.table
  base := (-7362561961747064116175603829681293739207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-382681143587094718880314834740000000000000)
      constant := (2542517287571103402427910518580078494429959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree055.table
  base := (-3681460844270079466188759313864637591959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-65547177901679896019210280465000000000000)
      constant := (451975315509388531305931587177592610568861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107351865678362037939/50000000000000000000)
  centralHi := (214703731356724075879/100000000000000000000)
  directionLo := (108341304711373062159/50000000000000000000)
  directionHi := (216682609422746124319/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree056.table
  base := (-7386091452498585226786620438640405118361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-390006109137520482060823566120000000000000)
      constant := (2657551261413818594823556389805654477543257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree056.table
  base := (-7386411178369742262683068803813311020247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-133600265070610711021226179560000000000000)
      constant := (944421995439041723863249092399920468574813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108341304711373062159/50000000000000000000)
  centralHi := (216682609422746124319/100000000000000000000)
  directionLo := (5466089449620287831/2500000000000000000)
  directionHi := (218643577984811513241/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree057.table
  base := (-7406167947823215431733130355864487346951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-397331074687946245241332297500000000000000)
      constant := (2775011890563000763489235482550537297142087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree057.table
  base := (-370322603992525859915977151175577940651/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-13610617433786163000403179819000000000000)
      constant := (98574141879735188394498258272375726492658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5466089449620287831/2500000000000000000)
  centralHi := (218643577984811513241/100000000000000000000)
  directionLo := (22058711467751320161/10000000000000000000)
  directionHi := (220587114677513201611/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree058.table
  base := (-3711397772205514760225271669503213145877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-202328020119186004210920514440000000000000)
      constant := (1447449458463587598345258491041297571809749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree058.table
  base := (-185576200250519351094962266467544571321/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-13861208360511254898683741682000000000000)
      constant := (102790882513590344646232110851726256009036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22058711467751320161/10000000000000000000)
  centralHi := (220587114677513201611/100000000000000000000)
  directionLo := (3476776191799854753/1562500000000000000)
  directionHi := (222513676275190704193/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree059.table
  base := (-3717988921062759786601687448735649958781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-205990502894398885801174880130000000000000)
      constant := (1508606056857470946685368205654654052596797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree059.table
  base := (-3718101070230480593204462105470370490391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-70558996436181733984821517725000000000000)
      constant := (535462073925753497641097703623872219701789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3476776191799854753/1562500000000000000)
  centralHi := (222513676275190704193/100000000000000000000)
  directionLo := (224423699945550253321/100000000000000000000)
  directionHi := (112211849972775126661/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree060.table
  base := (-7445718007399493013563979007436125004061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-419305971339223534782858491640000000000000)
      constant := (3141951281441033985844835469731524124744157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree060.table
  base := (-7445917255296730068433779652267066104433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-143623902139614386952448654080000000000000)
      constant := (1114787328477523850116663823502391611806907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224423699945550253321/100000000000000000000)
  centralHi := (112211849972775126661/50000000000000000000)
  directionLo := (113158802204026951133/50000000000000000000)
  directionHi := (226317604408053902267/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree061.table
  base := (-7452018828338716743829347697146885374461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-426630936889649297963367223020000000000000)
      constant := (3269116244454788159268103659569746221408957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree061.table
  base := (-3726097900732846414843428050992743998837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-73064905703432652967627136355000000000000)
      constant := (579749157814132078014818287887902376024423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113158802204026951133/50000000000000000000)
  centralHi := (226317604408053902267/100000000000000000000)
  directionLo := (228195791005772903173/100000000000000000000)
  directionHi := (114097895502886451587/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree062.table
  base := (-7454882762645862812323071461183552812583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-433955902440075061143875954400000000000000)
      constant := (3398706847920936074596154779665436172807271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree062.table
  base := (-3727519966151280675518470380378282601757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-74317860337058112459029945670000000000000)
      constant := (602528532041849481761434566427056065363103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228195791005772903173/100000000000000000000)
  centralHi := (114097895502886451587/50000000000000000000)
  directionLo := (230058644698477678679/100000000000000000000)
  directionHi := (5751466117461941967/2500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree063.table
  base := (-931788997415305941753908115980635651703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-110320216997625206081096171445000000000000)
      constant := (882680738798095550996215902108939907885422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree063.table
  base := (-7454451545349262159120517076904003285627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-151141629941367143900865509970000000000000)
      constant := (1251463533995447815536995342322515931001833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230058644698477678679/100000000000000000000)
  centralHi := (5751466117461941967/2500000000000000000)
  directionLo := (231906534983924931327/100000000000000000000)
  directionHi := (905884902280956763/390625000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree064.table
  base := (-7450308394974472144029957626934980412411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-448605833540926587504893417160000000000000)
      constant := (3665164445522948469624440285503096234018107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree064.table
  base := (-1862608078792580918579856439141931164501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-76823769604309031441835564300000000000000)
      constant := (649358845098827807621998274676038891090958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231906534983924931327/100000000000000000000)
  centralHi := (905884902280956763/390625000000000000)
  directionLo := (4674796335071738903/2000000000000000000)
  directionHi := (233739816753586945151/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree065.table
  base := (-7442873705434652875861621285110312372857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-455930799091352350685402148540000000000000)
      constant := (3802031212075173748801709092088050320510009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree065.table
  base := (-3721491860922928491402219703630184897929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-78076724237934490933238373615000000000000)
      constant := (673409750804320014917143264592516117143491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4674796335071738903/2000000000000000000)
  centralHi := (233739816753586945151/100000000000000000000)
  directionLo := (117779415544218093523/50000000000000000000)
  directionHi := (235558831088436187047/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree066.table
  base := (-148640188266348896284846528626949339229/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-46325576464177811386591087992000000000000)
      constant := (394132316018434737117955758486510958142865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree066.table
  base := (-1486421415144391778186078306966958252597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-31731871548623980169856473172000000000000)
      constant := (279153788142226605274882755639693876695463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117779415544218093523/50000000000000000000)
  centralHi := (235558831088436187047/100000000000000000000)
  directionLo := (237363905999839025659/100000000000000000000)
  directionHi := (11868195299991951283/5000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree067.table
  base := (-7417716852040030664291557950014915415409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-470580730192203877046419611300000000000000)
      constant := (4083040205845186826335458216119060328829233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree067.table
  base := (-1854450884729751118799431143668917574329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-80582633505185409916043992245000000000000)
      constant := (722782991550303364128934502624655461878182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237363905999839025659/100000000000000000000)
  centralHi := (11868195299991951283/5000000000000000000)
  directionLo := (119577678560058213861/50000000000000000000)
  directionHi := (239155357120116427723/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree068.table
  base := (-3699998603385502574859133631498755545779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-238952847871314820113464171340000000000000)
      constant := (2113591137196035323337873523135578400615923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree068.table
  base := (-3700037072015052653546409052849983638469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-81835588138810869407446801560000000000000)
      constant := (748105303546302896241719119590150343592151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119577678560058213861/50000000000000000000)
  centralHi := (239155357120116427723/100000000000000000000)
  directionLo := (60233372086722214763/25000000000000000000)
  directionHi := (240933488346888859053/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree069.table
  base := (-7378851532706923951770534338488567781581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-485230661293055403407437074060000000000000)
      constant := (4373749299347615824281795037325220229760397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree069.table
  base := (-737891981038334607102771011060104835589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-16617708554487265779769922175000000000000)
      constant := (154770279338124044067846868235487798452631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60233372086722214763/25000000000000000000)
  centralHi := (240933488346888859053/100000000000000000000)
  directionLo := (242698592444930417561/100000000000000000000)
  directionHi := (121349296222465208781/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree070.table
  base := (-7354280771023766460906856815877813709459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-492555626843481166587945805440000000000000)
      constant := (4522741221417735657554716837999697736304083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree070.table
  base := (-7354341358190892982496236096842692516861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-168682994812123576780504840380000000000000)
      constant := (1600042524742055182317589789116303457145919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242698592444930417561/100000000000000000000)
  centralHi := (121349296222465208781/50000000000000000000)
  directionLo := (244450951608907512299/100000000000000000000)
  directionHi := (2444509516089075123/1000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree071.table
  base := (-3663142881402237093425722871049901930427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-249940296196953464884227268410000000000000)
      constant := (2337078993807102415690943576168856178383099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree071.table
  base := (-7326339520864522650433541527239799724917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-171188904079374495763310459010000000000000)
      constant := (1653229785773402708613163504745464205776743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244450951608907512299/100000000000000000000)
  centralHi := (2444509516089075123/1000000000000000000)
  directionLo := (246190837990065033603/100000000000000000000)
  directionHi := (61547709497516258401/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree072.table
  base := (-1823716815301011948834896565068093738717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-126801389486083173237240817050000000000000)
      constant := (1206999887622064575955495754080710094460829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree072.table
  base := (-3647457477869778796879657281728638873013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-86847406673312707373058038820000000000000)
      constant := (853632281335620623333938188923698583666727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246190837990065033603/100000000000000000000)
  centralHi := (61547709497516258401/25000000000000000000)
  directionLo := (247918514189643478737/100000000000000000000)
  directionHi := (123959257094821739369/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree073.table
  base := (-3630012971039673027073024512065346150619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-257265261747379228064735999790000000000000)
      constant := (2492132933730456986252596939384883192511003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree073.table
  base := (-7260068253416770337026032469832505417401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-176200722613876333728921696270000000000000)
      constant := (1762146843032954573466126385871017386234579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247918514189643478737/100000000000000000000)
  centralHi := (123959257094821739369/50000000000000000000)
  directionLo := (249634233721560034817/100000000000000000000)
  directionHi := (124817116860780017409/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree074.table
  base := (-902720301660123595847069504927210708921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-130463872261296054827495182740000000000000)
      constant := (1285739225059395697452664813329171450675954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree074.table
  base := (-3610899972951905942023382448123748179021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-89353315940563626355863657450000000000000)
      constant := (908938307843191008963919533084401288240559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249634233721560034817/100000000000000000000)
  centralHi := (124817116860780017409/50000000000000000000)
  directionLo := (6283456036166545203/2500000000000000000)
  directionHi := (251338241446661808121/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree075.table
  base := (-3590038611389495101008254079129484240429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-264590227297804991245244731170000000000000)
      constant := (2652036307148076928402449443139842492852973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree075.table
  base := (-7180110513713517058702422519031141387057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-181212541148378171694532933530000000000000)
      constant := (1874453870540754048751515294537846030871803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6283456036166545203/2500000000000000000)
  centralHi := (251338241446661808121/100000000000000000000)
  directionLo := (253030773980657289273/100000000000000000000)
  directionHi := (126515386990328644637/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree076.table
  base := (-1783742716442849406504522058088792164669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-134126355036508936417749548430000000000000)
      constant := (1366903244609787548930081314500406093625853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree076.table
  base := (-1427000078411102375993703177738577099213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-36743690083125818135467710432000000000000)
      constant := (386375719691333703907733869883489880916527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253030773980657289273/100000000000000000000)
  centralHi := (126515386990328644637/50000000000000000000)
  directionLo := (63678015019412547731/25000000000000000000)
  directionHi := (10188482403106007637/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree077.table
  base := (-885805473863227030923577575559249610431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-135957596424115377212876731275000000000000)
      constant := (1408394491100443169603669233722034549085694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree077.table
  base := (-1771617494059861271082745448520066883451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-93112179841440004830072085395000000000000)
      constant := (995075395566311403411548279120907190895058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63678015019412547731/25000000000000000000)
  centralHi := (10188482403106007637/4000000000000000000)
  directionLo := (256382320991035742093/100000000000000000000)
  directionHi := (128191160495517871047/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree078.table
  base := (-879312050715858430041950015648044551957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-137788837811721818008003914120000000000000)
      constant := (1450491886627177539578220435338346386453418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree078.table
  base := (-1717412018162231277275064606609796957/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-94365134475065464321474894710000000000000)
      constant := (1024635220502973037583145594373925852473344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256382320991035742093/100000000000000000000)
  centralHi := (128191160495517871047/50000000000000000000)
  directionLo := (258041770813371401383/100000000000000000000)
  directionHi := (32255221351671425173/12500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree079.table
  base := (-3489564540724003699761642999128918692953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-279240158398656517606262193930000000000000)
      constant := (2986390850686757447575545673779878122343961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree079.table
  base := (-3489574835790137011163878288179037511541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-95618089108690923812877704025000000000000)
      constant := (1054618770583130367952066602536990212257639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258041770813371401383/100000000000000000000)
  centralHi := (32255221351671425173/12500000000000000000)
  directionLo := (10387624671868001153/4000000000000000000)
  directionHi := (129845308398350014413/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree080.table
  base := (-34601710785667159050724116478229009261/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-28290264117386939919651655962000000000000)
      constant := (307301020381757128038106880698715724165570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree080.table
  base := (-6920360413408385174864649413359569601289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-193742087484632766608561026680000000000000)
      constant := (2170052085279848853903788379919449038372931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10387624671868001153/4000000000000000000)
  centralHi := (129845308398350014413/50000000000000000000)
  directionLo := (52265811930936461999/20000000000000000000)
  directionHi := (65332264913670577499/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree081.table
  base := (-6858135943364752780932632836466123067813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-573130247898164561573541850620000000000000)
      constant := (6321683645726951592295878028992634246727781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree081.table
  base := (-428634508073246824814222599694105958771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-98123998375941842795683322655000000000000)
      constant := (1115857033761756492091797062860140198926472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52265811930936461999/20000000000000000000)
  centralHi := (65332264913670577499/25000000000000000000)
  directionLo := (131478646923892656647/50000000000000000000)
  directionHi := (52591458769557062659/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree082.table
  base := (-6792510725457536178000935362651732328931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-580455213448590324754050582000000000000000)
      constant := (6499771397674061340187116685872940863277347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree082.table
  base := (-3396262537305649053759274827592058529411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-99376953009567302287086131970000000000000)
      constant := (1147111741263353077175403627635566770882369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131478646923892656647/50000000000000000000)
  centralHi := (52591458769557062659/20000000000000000000)
  directionLo := (66143876963168574013/25000000000000000000)
  directionHi := (264575507852674296053/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree083.table
  base := (-210108336446388737151223419407269188673/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-146945044749754021983639828345000000000000)
      constant := (1670070911728873594106005054041236328908808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree083.table
  base := (-6723479486324625415976164781634545174761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-201259815286385523556977882570000000000000)
      constant := (2357580325320866300703018193623174551330019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66143876963168574013/25000000000000000000)
  centralHi := (264575507852674296053/100000000000000000000)
  directionLo := (133091942208432104251/50000000000000000000)
  directionHi := (266183884416864208503/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree084.table
  base := (-10392194232428794079649171551094666409/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-29755257227472092555753402238000000000000)
      constant := (343161018907399294678115617432993152519456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree084.table
  base := (-415688473992601901870779358140702152651/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-101882862276818221269891750600000000000000)
      constant := (1210892295647514868891026811452362038354632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133091942208432104251/50000000000000000000)
  centralHi := (266183884416864208503/100000000000000000000)
  directionLo := (267782600799604847537/100000000000000000000)
  directionHi := (133891300399802423769/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree085.table
  base := (-6575123577991224993331744656166524563613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-602430110099867614295576776140000000000000)
      constant := (7048581577188741345819916648111508952492381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree085.table
  base := (-6575133571676475288909397307894588126053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-206271633820887361522589119830000000000000)
      constant := (2486836276156919060657952954171713649352887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267782600799604847537/100000000000000000000)
  centralHi := (133891300399802423769/50000000000000000000)
  directionLo := (5387436579997969203/2000000000000000000)
  directionHi := (269371828999898460151/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree086.table
  base := (-3247912391624324258492030429261821254683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-304877537825146688738042753760000000000000)
      constant := (3618183615427385081294519821576505260954971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree086.table
  base := (-3247916820276688256217941779672488551183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-104388771544069140252697369230000000000000)
      constant := (1276367687949402861210304265241877740425157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5387436579997969203/2000000000000000000)
  centralHi := (269371828999898460151/100000000000000000000)
  directionLo := (67737933993120014263/25000000000000000000)
  directionHi := (270951735972480057053/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree087.table
  base := (-1282621623919140016353137717272148078703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-123416008240143828131318847780000000000000)
      constant := (1485315465371345052396037062405854671041711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree087.table
  base := (-6413115969233819224708830037463974509331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-211283452355389199488200357090000000000000)
      constant := (2619481886767538535461885419230756535304049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67737933993120014263/25000000000000000000)
  centralHi := (270951735972480057053/100000000000000000000)
  directionLo := (27252248383252811841/10000000000000000000)
  directionHi := (272522483832528118411/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree088.table
  base := (-6326973769400087247688130433129763710999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-624405006751144903837102970280000000000000)
      constant := (7619211853705441067712628991352824886207063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree088.table
  base := (-3163490362785309731691454249584190125913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-106894680811320059235502987860000000000000)
      constant := (1343537902619104181495517756758732007355827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27252248383252811841/10000000000000000000)
  centralHi := (272522483832528118411/100000000000000000000)
  directionLo := (137042115024908087563/50000000000000000000)
  directionHi := (274084230049816175127/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree089.table
  base := (-124748438072704679919979303974753971559/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-63172997230157066701761170166000000000000)
      constant := (781427080062959186896777321672952498958915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree089.table
  base := (-6237428067650791972789602788680431798297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-216295270889891037453811594350000000000000)
      constant := (2755517127990987895377097652615210932235763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137042115024908087563/50000000000000000000)
  centralHi := (274084230049816175127/100000000000000000000)
  directionLo := (137818563816481706147/50000000000000000000)
  directionHi := (55127425526592682459/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree090.table
  base := (-6144452683032657735069776721170713595181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-639054937851996430198120433040000000000000)
      constant := (8011754157503092069018208206366245043503597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree090.table
  base := (-6144458144766341783435385609410513722603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-218801180157141956436617212980000000000000)
      constant := (2824805851890745026979435909752379211825337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137818563816481706147/50000000000000000000)
  centralHi := (55127425526592682459/20000000000000000000)
  directionLo := (69295331326098625849/25000000000000000000)
  directionHi := (277181325304394503397/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree091.table
  base := (-6048066259098829835670984057417091985293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-646379903402422193378629164420000000000000)
      constant := (8211661914781033971505397559672723204926541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree091.table
  base := (-1512017774567407680772692802377338437999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-110653544712196437709711415805000000000000)
      constant := (1447470986984540079707434742858901785604042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69295331326098625849/25000000000000000000)
  centralHi := (277181325304394503397/100000000000000000000)
  directionLo := (139358483833287464981/50000000000000000000)
  directionHi := (278716967666574929963/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree092.table
  base := (-5948262775013226496618581574807126919597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-653704868952847956559137895800000000000000)
      constant := (8413994063443110575903933631507151004065389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree092.table
  base := (-5948267062327825483647580783987867874153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-223812998691643794402228450240000000000000)
      constant := (2965925491408482792153670135416254774642787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139358483833287464981/50000000000000000000)
  centralHi := (278716967666574929963/100000000000000000000)
  directionLo := (56048839072009540161/20000000000000000000)
  directionHi := (140122097680023850403/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree093.table
  base := (-116900847328443494124582241367210006877/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (88)
      previous := (38)
      next := (0)
      square := (1214402183360060737821184413000000000000)
      linear := (-66102983450327371973964662718000000000000)
      constant := (861875059494360328194987422578328847833745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree093.table
  base := (-2922523082294534645758212893897608833341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-113159453979447356692517034435000000000000)
      constant := (1518878200764170958720607509146900214499839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56048839072009540161/20000000000000000000)
  centralHi := (140122097680023850403/50000000000000000000)
  directionLo := (56352629042752064877/20000000000000000000)
  directionHi := (140881572606880162193/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree094.table
  base := (-1147681032428252815481712984397035982361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-133670960010739896584031071712000000000000)
      constant := (1765186300233425988806028402262986733111257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree094.table
  base := (-1434602131692849405980650788057884638411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-114412408613072816183919843750000000000000)
      constant := (1555217350886289395127886449396568845186738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56352629042752064877/20000000000000000000)
  centralHi := (140881572606880162193/50000000000000000000)
  directionLo := (28327395038813680849/10000000000000000000)
  directionHi := (283273950388136808491/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree095.table
  base := (-2814175642388747401799530380950176341399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-337839882802062623050332044970000000000000)
      constant := (4517768387194724774978941694325138890491863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree095.table
  base := (-1407088566296001936545316014198192316493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-115665363246698275675322653065000000000000)
      constant := (1591980194849350134012862801072425922707294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28327395038813680849/10000000000000000000)
  centralHi := (283273950388136808491/100000000000000000000)
  directionLo := (17798546281957380891/6250000000000000000)
  directionHi := (284776740511318094257/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree096.table
  base := (-1378720212820233709225747231426847929167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-170751182788637752320293205330000000000000)
      constant := (2311891601810676954687661957380108580462479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree096.table
  base := (-551488349118926435579989901168187212473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-23383663576064747033345092476000000000000)
      constant := (325833346296809669210341582763468068538067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17798546281957380891/6250000000000000000)
  centralHi := (284776740511318094257/100000000000000000000)
  directionLo := (35783955226120679313/12500000000000000000)
  directionHi := (57254328361793086901/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree097.table
  base := (-5397993973434439476480196208712095407969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-690329696704976772461681552700000000000000)
      constant := (9462020392684584866561364985821137989297953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree097.table
  base := (-5397996311612755243478166548949596720839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-236342545027898389316256543390000000000000)
      constant := (3333553919337430718884150746089558468862381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35783955226120679313/12500000000000000000)
  centralHi := (57254328361793086901/20000000000000000000)
  directionLo := (287758777227994581407/100000000000000000000)
  directionHi := (8992461788374830669/3125000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree098.table
  base := (-5277690758288921125328176786041202439773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-697654662255402535642190284080000000000000)
      constant := (9678898723970873212001192724519404246294301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree098.table
  base := (-5277692829107780751647425826484851845021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-238848454295149308299062162020000000000000)
      constant := (3409621756650983041176871815193818111254559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287758777227994581407/100000000000000000000)
  centralHi := (8992461788374830669/3125000000000000000)
  directionLo := (289238266554584058527/100000000000000000000)
  directionHi := (9038695829830751829/3125000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree099.table
  base := (-322123206784420389503355432269576613161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-176244906951457074705674753865000000000000)
      constant := (2474550348657768257201976350330566693483428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree099.table
  base := (-5153973142479850828955445187934574533757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-241354363562400227281867780650000000000000)
      constant := (3486536972833837950059975899730873934791103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289238266554584058527/100000000000000000000)
  centralHi := (9038695829830751829/3125000000000000000)
  directionLo := (145355113263389039871/50000000000000000000)
  directionHi := (290710226526778079743/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree100.table
  base := (-157088616341464473498317354054914197457/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-178076148339063515500801936710000000000000)
      constant := (2529982099611660697649567251556323244481672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree100.table
  base := (-1005367469395211588129640825900733917377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42000000000000000000000000000000000000000
      center := (58)
      previous := (26)
      next := (0)
      square := (809601455573373825214122942000000000000)
      linear := (-48772054565930229252934679856000000000000)
      constant := (712859913177161300752659486056084587735083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145355113263389039871/50000000000000000000)
  centralHi := (290710226526778079743/100000000000000000000)
  directionLo := (146087385470991840719/50000000000000000000)
  directionHi := (292174770941983681439/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree101.table
  base := (-4896284096433113839045932068140515686069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-719629558906679825183716478220000000000000)
      constant := (10344079729431588234267741486597147511777653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree101.table
  base := (-153008922954486855390389876169985714639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-123183091048451032623739508955000000000000)
      constant := (1821454766937998989642867082865634799881296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146087385470991840719/50000000000000000000)
  centralHi := (292174770941983681439/100000000000000000000)
  directionLo := (293632010759642209247/100000000000000000000)
  directionHi := (9176000336238819039/3125000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree102.table
  base := (-4762316520669440855326210602988469419177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-726954524457105588364225209600000000000000)
      constant := (10570655381815111718412011653731726426591849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree102.table
  base := (-4762317794061026729473318816301423607941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-248872091364152984230284636540000000000000)
      constant := (3722366874937961532922599890087670104233239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293632010759642209247/100000000000000000000)
  centralHi := (9176000336238819039/3125000000000000000)
  directionLo := (9221314193729291079/3125000000000000000)
  directionHi := (295082054199337314529/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree103.table
  base := (-4624933084066557776425724386148677045081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-734279490007531351544733940980000000000000)
      constant := (10799655350026078287765839300162633346159897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree103.table
  base := (-4624934211545893408049890898869248741957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-251378000631403903213090255170000000000000)
      constant := (3802671587265329803348252276261245776418903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9221314193729291079/3125000000000000000)
  centralHi := (295082054199337314529/100000000000000000000)
  directionLo := (18532812927161559319/6250000000000000000)
  directionHi := (59305001366916989821/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree104.table
  base := (-1121033468026763942935905750077953051869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-185401113889489278681310668090000000000000)
      constant := (2757769907169771174664269500545088957732253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree104.table
  base := (-1121033717585235897662720413685687713033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-126941954949327411097947936900000000000000)
      constant := (1941911834553952371365844423745201116052614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18532812927161559319/6250000000000000000)
  centralHi := (59305001366916989821/20000000000000000000)
  directionLo := (148980485841267695451/50000000000000000000)
  directionHi := (297960971682535390903/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree105.table
  base := (-4339918967524063300087884265210222677637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-748929421108382877905751403740000000000000)
      constant := (11264928212561943858180825157141755971308869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree105.table
  base := (-4339919851282031122671816661132582467183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-256389819165905741178701492430000000000000)
      constant := (3965823118768133420319603566653715768189157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148980485841267695451/50000000000000000000)
  centralHi := (297960971682535390903/100000000000000000000)
  directionLo := (149695024644901494647/50000000000000000000)
  directionHi := (59878009857960597859/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree106.table
  base := (-4192288450480051958774327767108017698259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-756254386658808641086260135120000000000000)
      constant := (11501201096624420055706184131112194885009683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree106.table
  base := (-1048072308212381687630850669847938286971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-129447864216578330080753555530000000000000)
      constant := (2024334967298964025218685795881386591947218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149695024644901494647/50000000000000000000)
  centralHi := (59878009857960597859/20000000000000000000)
  directionLo := (300812337814625997319/100000000000000000000)
  directionHi := (7520308445365649933/2500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree107.table
  base := (-2020621199364041493416525870302104338149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-381789676104617202133384433250000000000000)
      constant := (5869949137984035216587129367655967426696613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree107.table
  base := (-4041243091305261770264370301935985560979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-261401637700407579144312729690000000000000)
      constant := (4132364114995790175867759580376844303219441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300812337814625997319/100000000000000000000)
  centralHi := (7520308445365649933/2500000000000000000)
  directionLo := (302227933105546476803/100000000000000000000)
  directionHi := (75556983276386619201/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree108.table
  base := (-485847610969688753018432418467091857217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-192726079439915041861819399470000000000000)
      constant := (2995254936459266427818098642633146425990658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree108.table
  base := (-3886781500816660070605214478855880606597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-263907546967658498127118348320000000000000)
      constant := (4216905658404203894947847138544026507261463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302227933105546476803/100000000000000000000)
  centralHi := (75556983276386619201/25000000000000000000)
  directionLo := (303636928776788747127/100000000000000000000)
  directionHi := (37954616097098593391/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree109.table
  base := (-46611299886573868392313824247475180687/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-38911464165504296531389316463000000000000)
      constant := (611228275080493928837926782482136254466876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree109.table
  base := (-3728904533569524425826892788384414402063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-266413456234909417109923966950000000000000)
      constant := (4302294563307267349417734157121427297556677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303636928776788747127/100000000000000000000)
  centralHi := (37954616097098593391/12500000000000000000)
  directionLo := (61007883256100826199/20000000000000000000)
  directionHi := (76259854070126032749/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree110.table
  base := (-1783805889789397910342973273294557698333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-392777124430255846904147530320000000000000)
      constant := (6235267769395870808313932402882442865005021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree110.table
  base := (-445951532483845356731927435130660944887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-134459682751080168046364792790000000000000)
      constant := (2194265414114267735450487168424024480629492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61007883256100826199/20000000000000000000)
  centralHi := (76259854070126032749/25000000000000000000)
  directionLo := (306435484976039769031/100000000000000000000)
  directionHi := (38304435622004971129/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree111.table
  base := (-3402904323158491829068867038156768366751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-792879214410937456988803792020000000000000)
      constant := (12718929853007788497188192229086123592894687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree111.table
  base := (-1701452374121091776543780324360879997851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-135712637384705627537767602105000000000000)
      constant := (2237807225864525143615617794897171520045129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306435484976039769031/100000000000000000000)
  centralHi := (38304435622004971129/12500000000000000000)
  directionLo := (307825222196379972537/100000000000000000000)
  directionHi := (153912611098189986269/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree112.table
  base := (-101086927790729970743109123677649365639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-200051044990340805042328130850000000000000)
      constant := (3242437109999200609925760893346464719717944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree112.table
  base := (-808695516376587363536518795795214671241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-136965592018331087029170411420000000000000)
      constant := (2281772716202768988432719989616600983807878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307825222196379972537/100000000000000000000)
  centralHi := (153912611098189986269/50000000000000000000)
  directionLo := (77302178327974977109/25000000000000000000)
  directionHi := (309208713311899908437/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree113.table
  base := (-3063243943938450260879139745673825792261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-807529145511788983349821254780000000000000)
      constant := (13222991295605505121800555776912548975087557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree113.table
  base := (-3063244276865363232654849759028372145861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-276437093303913093041146441470000000000000)
      constant := (4652323768888754383615485884997904184936919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77302178327974977109/25000000000000000000)
  centralHi := (309208713311899908437/100000000000000000000)
  directionLo := (310586041791563314871/100000000000000000000)
  directionHi := (38823255223945414359/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree114.table
  base := (-722072787839629643029810605012455877747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-203713527765553686632582496540000000000000)
      constant := (3369664603945831773730097155634215279701939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree114.table
  base := (-361036430746668564711205134655468876863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-139471501285582006011976030050000000000000)
      constant := (2370974729920981455635391208183940614343508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310586041791563314871/100000000000000000000)
  centralHi := (38823255223945414359/12500000000000000000)
  directionLo := (311957289261688386467/100000000000000000000)
  directionHi := (77989322315422096617/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree115.table
  base := (-3387404217880259897389455393219195467/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-41108953830632025485541935877000000000000)
      constant := (686837489828880389603830047861587627423160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree115.table
  base := (-2709923635003301074629954860281024603789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-281448911838414931006757678730000000000000)
      constant := (4832422503959530648758359953171598483320431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311957289261688386467/100000000000000000000)
  centralHi := (77989322315422096617/25000000000000000000)
  directionLo := (313322535562398905141/100000000000000000000)
  directionHi := (156661267781199452571/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree116.table
  base := (-101125626961286055298520907459078327169/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (176)
      previous := (76)
      next := (0)
      square := (2428804366720121475642368826000000000000)
      linear := (-165900808432613254578269489784000000000000)
      constant := (2799453086825835865792831398758390326941765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree116.table
  base := (-158008806544306454087149380240946137349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-141977410552832924994781648680000000000000)
      constant := (2461871449982815133238963958459521048925368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313322535562398905141/100000000000000000000)
  centralHi := (156661267781199452571/50000000000000000000)
  directionLo := (157340929400935544457/50000000000000000000)
  directionHi := (62936371760374217783/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree117.table
  base := (-1171471555189809595640443343087781395677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-418414503856746018035928090150000000000000)
      constant := (7130102662334146840688049387870469772072349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree117.table
  base := (-585735828620456158527931370770505740909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-143230365186458384486184457995000000000000)
      constant := (2507955323306518352001390977086388758881822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157340929400935544457/50000000000000000000)
  centralHi := (62936371760374217783/20000000000000000000)
  directionLo := (158017667704240226861/50000000000000000000)
  directionHi := (316035335408480453723/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree118.table
  base := (-2154330741824282824405435786612791877779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-844153973263917799252364911680000000000000)
      constant := (14525569464510857546069888696283394111699923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree118.table
  base := (-2154330922404969760541417974599525864569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-288966639640167687955174534620000000000000)
      constant := (5108925742682008965157973469683409956844051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158017667704240226861/50000000000000000000)
  centralHi := (316035335408480453723/100000000000000000000)
  directionLo := (317383040180947201083/100000000000000000000)
  directionHi := (79345760045236800271/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree119.table
  base := (-245287953192449493672454163050790861497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-212869734703585890608218410765000000000000)
      constant := (3698339462513735835497580016618100351451378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree119.table
  base := (-981151892651040229204318132458663638147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-145736274453709303468990076625000000000000)
      constant := (2601394093489624235927636960307118063598913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317383040180947201083/100000000000000000000)
  centralHi := (79345760045236800271/25000000000000000000)
  directionLo := (159362523168286614473/50000000000000000000)
  directionHi := (318725046336573228947/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree120.table
  base := (-883430908723117488577099649763628585471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-429401952182384662806691187220000000000000)
      constant := (7531785238888774227623748761264891399115327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree120.table
  base := (-176686195878405200526684604749394950969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-29397845817466952592078577188000000000000)
      constant := (529749797833692642326606052740262706029651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159362523168286614473/50000000000000000000)
  centralHi := (318725046336573228947/100000000000000000000)
  directionLo := (320061425557658788273/100000000000000000000)
  directionHi := (160030712778829394137/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree121.table
  base := (-1568005372259991163887998936769641286303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-866128869915195088793891105820000000000000)
      constant := (15336207344231578036703412559073512598962911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree121.table
  base := (-392001374323070382938237160923603977699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-148242183720960222451795695255000000000000)
      constant := (2696527557805886739823479181149958632936642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320061425557658788273/100000000000000000000)
  centralHi := (160030712778829394137/50000000000000000000)
  directionLo := (160696124018091024791/50000000000000000000)
  directionHi := (321392248036182049583/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree122.table
  base := (-34143358588411535951028180173034853089/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-43672691773281042598719991860000000000000)
      constant := (780563422302151473993253959584197608510786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree122.table
  base := (-341433613534832559136729715745340457387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-149495138354585681943198504570000000000000)
      constant := (2744729798842112927912843977153695700789746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160696124018091024791/50000000000000000000)
  centralHi := (321392248036182049583/100000000000000000000)
  directionLo := (161358791258410189871/50000000000000000000)
  directionHi := (322717582516820379743/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree123.table
  base := (-1160048783712845769045463341937521851579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-880778801016046615154908568580000000000000)
      constant := (15888753779908359186658289028747936123350523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree123.table
  base := (-1160048881547149087882146379784112547813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (290)
      previous := (130)
      next := (0)
      square := (4048007277866869126070614710000000000000)
      linear := (-301496185976422282869202627770000000000000)
      constant := (5586711423457622581469348120262033636495927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161358791258410189871/50000000000000000000)
  centralHi := (322717582516820379743/100000000000000000000)
  directionLo := (324037496338387939259/100000000000000000000)
  directionHi := (16201874816919396963/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree124.table
  base := (-950948744147124249441692543650534918867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-888103766566472378335417299960000000000000)
      constant := (16168663342592014411252978902550016300111379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree124.table
  base := (-475474415341544781911662654658397928079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-152001047621836600926004123200000000000000)
      constant := (2842405295928724637769290141872173643510341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324037496338387939259/100000000000000000000)
  centralHi := (16201874816919396963/5000000000000000000)
  directionLo := (325352055473760275213/100000000000000000000)
  directionHi := (162676027736880137607/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree125.table
  base := (-36921713757742827870380425029095029577/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-44771436605844907075796301567000000000000)
      constant := (822549856546205744696197390535667013136649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree125.table
  base := (-36921717584694814183340054377052261023/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-30650800451092412083481386503000000000000)
      constant := (578375710183062430102816119059913805037034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325352055473760275213/100000000000000000000)
  centralHi := (162676027736880137607/50000000000000000000)
  directionLo := (163330662284176443747/50000000000000000000)
  directionHi := (65332264913670577499/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree126.table
  base := (-522505426043819593808556030363453503379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (880)
      previous := (380)
      next := (0)
      square := (12144021833600607378211844130000000000000)
      linear := (-902753697667323904696434762720000000000000)
      constant := (16735755141798270689916679029727102429287123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree126.table
  base := (-10450109874757133312742754877720277719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-30901391377817503981761948366000000000000)
      constant := (588355095234482362215537499620839370839505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163330662284176443747/50000000000000000000)
  centralHi := (65332264913670577499/20000000000000000000)
  directionLo := (16398268348860863493/5000000000000000000)
  directionHi := (327965366977217269861/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree127.table
  base := (-151581122573337701560105399362496838571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (440)
      previous := (190)
      next := (0)
      square := (6072010916800303689105922065000000000000)
      linear := (-455039331608874833938471747050000000000000)
      constant := (8511468686084762045214602496325162699170027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree127.table
  base := (-75790576253815909905751256931154029599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105000000000000000000000000000000000000000
      center := (145)
      previous := (65)
      next := (0)
      square := (2024003638933434563035307355000000000000)
      linear := (-155759911522712979400212551145000000000000)
      constant := (2992096071193920543696279817917641530756842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16398268348860863493/5000000000000000000)
  centralHi := (327965366977217269861/100000000000000000000)
  directionLo := (329264244800814657807/100000000000000000000)
  directionHi := (20579015300050916113/6250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree128.table
  base := (-10050597481480075200669911976298115363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (220)
      previous := (95)
      next := (0)
      square := (3036005458400151844552961032500000000000)
      linear := (-229350907192043857764363056370000000000000)
      constant := (4328135954763101212159242537650986437464262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree128.table
  base := (-8040483279733062306890156725131290621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-31402573231267687778323072092000000000000)
      constant := (608568067096698121497338063828772242896959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell007.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329264244800814657807/100000000000000000000)
  centralHi := (20579015300050916113/6250000000000000000)
  directionLo := (82639504729881159579/25000000000000000000)
  directionHi := (330558018919524638317/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree129.table
  base := (7288346168364494588187833429811367251/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (44)
      previous := (19)
      next := (0)
      square := (607201091680030368910592206500000000000)
      linear := (-46236429715930059711898047843000000000000)
      constant := (880228723975954454232236163478578116136813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 13
  qDenominator := 42
  table := BinomialMassData.Q13_42.Degree129.table
  base := (14576687654631685026281003384861940001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21000000000000000000000000000000000000000
      center := (29)
      previous := (13)
      next := (0)
      square := (404800727786686912607061471000000000000)
      linear := (-31653164157992779676603633955000000000000)
      constant := (618801653710848186868882838888832100740021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_42.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell007.Kernel129
