import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell130.Parameters
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94453_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch000_049
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch050_099
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree000.table
  base := (1163032813361852742883684191/20000000000000000000000000)
  polynomial :=
    { denominator := 14314240000000000000000000000000000000000000
      center := (94453)
      previous := (0)
      next := (84475)
      square := (2182099544017685037715637059520000000000000)
      linear := (-10171502681544502732435830747904000000000000)
      constant := (832396540916838350314767379708992000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree000.table
  base := (1163032813361852742883684191/20000000000000000000000000)
  polynomial :=
    { denominator := 7157120000000000000000000000000000000000000
      center := (47239)
      previous := (0)
      next := (42225)
      square := (1091049772008842518857818529760000000000000)
      linear := (-5085751340772251366217915373952000000000000)
      constant := (416198270458419175157383689854496000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree001.table
  base := (350162859431162691868985521870072145943973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-17438893189574996833156159831458219000000000000000)
      constant := (709014704926860587390812502993123138719436976156752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree001.table
  base := (350101872340156019386116200636279782535227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-8719872786104689370687008751092297000000000000000)
      constant := (354447554667551219163300792945889771781592904952024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49921412498889217363/100000000000000000000)
  directionHi := (12480353124722304341/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree002.table
  base := (44034654767298708890019063259247259696309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-4131859413637194381841716551238026800000000000000)
      constant := (91793498950465385315847793450351197381331179617616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree002.table
  base := (110052473791095775165023308444778415470307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-10330500916727367862822149048821442000000000000000)
      constant := (229418275261423855111369314679483873961140609489968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/100000000000000000000)
  centralHi := (12480353124722304341/25000000000000000000)
  directionLo := (70599538608750872963/100000000000000000000)
  directionHi := (17649884652187718241/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree003.table
  base := (145528339977651321031051171600189631716971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-23879700946796946985261005680922049000000000000000)
      constant := (321362261988344613231430541922740403861211374205104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree003.table
  base := (145469771352148712457643847351628108258903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-11941129047350046354957289346550587000000000000000)
      constant := (160627539506850008427293542554480288857660711044536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/100000000000000000000)
  centralHi := (17649884652187718241/25000000000000000000)
  directionLo := (86466422833680113569/100000000000000000000)
  directionHi := (8646642283368011357/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree004.table
  base := (20262187780754375473324034764892766723149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-5420020965081584412262685721130792800000000000000)
      constant := (49268210404271414308737864903609022439091494573776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree004.table
  base := (101265023954604887975811203235546327604851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-13551757177972724847092429644279732000000000000000)
      constant := (123132162594188173349097639552577755928714079849112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/100000000000000000000)
  centralHi := (8646642283368011357/10000000000000000000)
  directionLo := (49921412498889217363/50000000000000000000)
  directionHi := (99842824997778434727/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree005.table
  base := (73997389493992776858500189938851890434007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-30320508704018897137365851530385879000000000000000)
      constant := (206843630445380244551558306647786740661024458278768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree005.table
  base := (73962318398968649393663075337838633270119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-15162385308595403339227569942008877000000000000000)
      constant := (103397319211137456038455954118256176292255848873528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49921412498889217363/50000000000000000000)
  centralHi := (99842824997778434727/100000000000000000000)
  directionLo := (111627671880323934613/100000000000000000000)
  directionHi := (55813835940161967307/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree006.table
  base := (5622249513610067326748105599437462334349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-6708182516525974442683654891023558800000000000000)
      constant := (37626518733017443284109274087783271688693858805152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree006.table
  base := (14048875277827381137927307343691695318897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-16773013439218081831362710239738022000000000000000)
      constant := (94053350142887707937011884651398863533998427636256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111627671880323934613/100000000000000000000)
  centralHi := (55813835940161967307/50000000000000000000)
  directionLo := (4891279514451083249/4000000000000000000)
  directionHi := (61140993930638540613/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree007.table
  base := (10988672502042421138318165139888579266451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-36761316461240847289470697379849709000000000000000)
      constant := (182140972695519334289326175933455380141144841826496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree007.table
  base := (1757333407910800173397982044700044808833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400190364800000000000000000000000000000000000000
      center := (2641368685)
      previous := (0)
      next := (2361010875)
      square := (61006048001874429441934923091530400000000000000)
      linear := (-735345662793630412939914021498686680000000000000)
      constant := (3642683999262751616595495159552531819058061330696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4891279514451083249/4000000000000000000)
  centralHi := (61140993930638540613/50000000000000000000)
  directionLo := (66039821284566193197/50000000000000000000)
  directionHi := (26415928513826477279/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree008.table
  base := (17485213222403972709134113345279126556547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-39981720339851822365523120304581624000000000000000)
      constant := (184419555779859803615889139970880582144899117583456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree008.table
  base := (34952900506813662671839534035941120806479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-19994269700463438815632990835196312000000000000000)
      constant := (92214590661269119396933369711207189617164253033848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66039821284566193197/50000000000000000000)
  centralHi := (26415928513826477279/20000000000000000000)
  directionLo := (70599538608750872963/50000000000000000000)
  directionHi := (141199077217501745927/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree009.table
  base := (5605881796247036572022607329822560821917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-8640424843692559488315108645862707800000000000000)
      constant := (38497314289111521875391126759557639029215760326608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree009.table
  base := (28014478329184516584627645248274876719963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-21604897831086117307768131132925457000000000000000)
      constant := (96255513475722352472027416249251790775592551031256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/50000000000000000000)
  centralHi := (141199077217501745927/100000000000000000000)
  directionLo := (149764237496667652089/100000000000000000000)
  directionHi := (14976423749666765209/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree010.table
  base := (5607040837228760450554195451784992604081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-46422528097073772517627966154045454000000000000000)
      constant := (204934401571847866071710619664102608152849547174976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree010.table
  base := (22415030398657693371138054796589064366357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-23215525961708795799903271430654602000000000000000)
      constant := (102486495574356261326376250741446844911157721692584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149764237496667652089/100000000000000000000)
  centralHi := (14976423749666765209/10000000000000000000)
  directionLo := (157865367509287880971/100000000000000000000)
  directionHi := (39466341877321970243/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree011.table
  base := (17758002536681555052952354901886163846239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-49642931975684747593680389078777369000000000000000)
      constant := (220945283138292923281343679764573381619744782589936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree011.table
  base := (17746169321646847210050588175418258145017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-24826154092331474292038411728383747000000000000000)
      constant := (110498955207123243673647182555437681361587311330504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157865367509287880971/100000000000000000000)
  centralHi := (39466341877321970243/25000000000000000000)
  directionLo := (2069632428292173603/1250000000000000000)
  directionHi := (165570594263373888241/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree012.table
  base := (13773519443019101765463664827889947008487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-52863335854295722669732812003509284000000000000000)
      constant := (240028168357492546307845693936217276037895406130288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree012.table
  base := (13762682012903976174676944367364766423843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-26436782222954152784173552026112892000000000000000)
      constant := (120047562588925471040058976591112816724561303969816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/1250000000000000000)
  centralHi := (165570594263373888241/100000000000000000000)
  directionLo := (86466422833680113569/50000000000000000000)
  directionHi := (172932845667360227139/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree013.table
  base := (2580227785433534087865316242882643581463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-56083739732906697745785234928241199000000000000000)
      constant := (261875304983743222729301740937559237300331129754048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree013.table
  base := (10310885813600786484163347483939446926287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-28047410353576831276308692323842037000000000000000)
      constant := (130978561921513121353808023277792466078852583098744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/50000000000000000000)
  centralHi := (172932845667360227139/100000000000000000000)
  directionLo := (44998553127083488661/25000000000000000000)
  directionHi := (35998842501666790929/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree014.table
  base := (7298736332888235526235174819509143825489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-59304143611517672821837657852973114000000000000000)
      constant := (286283713862904233386487313949509371247290552241936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree014.table
  base := (1457882254847589960153575064704336297477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-5931607696839901953688766524314236400000000000000)
      constant := (28638107102489883230560905796035438717573004874024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44998553127083488661/25000000000000000000)
  centralHi := (35998842501666790929/20000000000000000000)
  directionLo := (93394410917328902051/50000000000000000000)
  directionHi := (186788821834657804103/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree015.table
  base := (4636285952219491895855810235719503603727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-62524547490128647897890080777705029000000000000000)
      constant := (313111909563867381465799925067364608969502113848048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree015.table
  base := (925518151636584017091048256353555159821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-6253733322964437652115794583860065400000000000000)
      constant := (31322556418705104865952535546520971705464220731752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93394410917328902051/50000000000000000000)
  centralHi := (186788821834657804103/100000000000000000000)
  directionLo := (193344799227348726231/100000000000000000000)
  directionHi := (24168099903418590779/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree016.table
  base := (2281542860484522155334457770772132056073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-65744951368739622973942503702436944000000000000000)
      constant := (342255808296984357163191259815155655525968139627152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree016.table
  base := (568357528239033761037210047396628725341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-32879294745444866752714113217029472000000000000000)
      constant := (171193282767620788737155365780665013398843737943968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/100000000000000000000)
  centralHi := (24168099903418590779/12500000000000000000)
  directionLo := (199685649995556869453/100000000000000000000)
  directionHi := (99842824997778434727/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree017.table
  base := (194380910586809088638180595990080519001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-68965355247350598049994926627168859000000000000000)
      constant := (373635119575032292051192811201464594981651917607824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree017.table
  base := (186815375306674554810853573065920055897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-34489922876067545244849253514758617000000000000000)
      constant := (186891904480767810581047655388180123066542642053064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/100000000000000000000)
  centralHi := (99842824997778434727/50000000000000000000)
  directionLo := (102915628356474962727/50000000000000000000)
  directionHi := (41166251342589985091/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree018.table
  base := (-414339532549473772717717121597193738791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-72185759125961573126047349551900774000000000000000)
      constant := (407185496323584986032103616048496016705339075980864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree018.table
  base := (-166440559863913298206730945513955825539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-7220110201338044747396878762497552400000000000000)
      constant := (40735295957500364611026538067059651923432312166864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/50000000000000000000)
  centralHi := (41166251342589985091/20000000000000000000)
  directionLo := (211798615826252618889/100000000000000000000)
  directionHi := (21179861582625261889/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree019.table
  base := (-3300194580681702687160412851415788982839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-75406163004572548202099772476632689000000000000000)
      constant := (442853872662342281478006615831813476583639198251664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree019.table
  base := (-206671894760671370958088239435191574709/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-37711179137312902229119534110216907000000000000000)
      constant := (221520478560533442651759122513179912072872753446272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211798615826252618889/100000000000000000000)
  centralHi := (21179861582625261889/10000000000000000000)
  directionLo := (217602392201466385667/100000000000000000000)
  directionHi := (54400598050366596417/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree020.table
  base := (-4756448792605607752375423533204624488551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-78626566883183523278152195401364604000000000000000)
      constant := (480595586642775714764689179648280074564398809432976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree020.table
  base := (-1190634489411676147663438104570766189153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-39321807267935580721254674407946052000000000000000)
      constant := (240401570997538354285913271327377710313473551269856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/100000000000000000000)
  centralHi := (54400598050366596417/25000000000000000000)
  directionLo := (223255343760647869227/100000000000000000000)
  directionHi := (55813835940161967307/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree021.table
  base := (-6045171165937396375731879252589680778303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-81846970761794498354204618326096519000000000000000)
      constant := (520372519332321814775692768146497032554326872525328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree021.table
  base := (-1210163694514512802676710858676727850861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-8186487079711651842677962941135039400000000000000)
      constant := (52060139616582289162048120015525378302734041039768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/100000000000000000000)
  centralHi := (55813835940161967307/25000000000000000000)
  directionLo := (228768651575274412739/100000000000000000000)
  directionHi := (11438432578763720637/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree022.table
  base := (-7182776016867014503547637358694196141819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-85067374640405473430257041250828434000000000000000)
      constant := (562151826475060596439271258579964402096813509272144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree022.table
  base := (-7188005954618875900707743247158474036201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-42543063529180937705524955003404342000000000000000)
      constant := (281201437911318014586049222396982774530103483509688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/100000000000000000000)
  centralHi := (11438432578763720637/5000000000000000000)
  directionLo := (234152179937436321573/100000000000000000000)
  directionHi := (117076089968718160787/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree023.table
  base := (-4091748567612236189884378062603389871937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-88287778519016448506309464175560349000000000000000)
      constant := (605905026943269268107862100688334669475579066873824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree023.table
  base := (-4094166976432568839064872956929609668387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-44153691659803616197660095301133487000000000000000)
      constant := (303089550159761753666056945464417349156932997212112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/100000000000000000000)
  centralHi := (117076089968718160787/50000000000000000000)
  directionLo := (59853670937617628087/25000000000000000000)
  directionHi := (239414683750470512349/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree024.table
  base := (-9059731477715979186672965993219402318221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-91508182397627423582361887100292264000000000000000)
      constant := (651607315023814491486061121270924531299165861614896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree024.table
  base := (-9064199057614702055074580554046306232997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-45764319790426294689795235598862632000000000000000)
      constant := (325952632338253225891644103140079764481311041931736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/25000000000000000000)
  centralHi := (239414683750470512349/100000000000000000000)
  directionLo := (244563975722554162451/100000000000000000000)
  directionHi := (61140993930638540613/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree025.table
  base := (-9822309191625671280246300376838417992743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-94728586276238398658414310025024179000000000000000)
      constant := (699237020113733885286093353449252930945396475386768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree025.table
  base := (-9826430891649799185532506967011754079799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-47374947921048973181930375896591777000000000000000)
      constant := (349779849670062763572103389812156400484793374698312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244563975722554162451/100000000000000000000)
  centralHi := (61140993930638540613/25000000000000000000)
  directionLo := (7800220702951440213/3125000000000000000)
  directionHi := (249607062494446086817/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree026.table
  base := (-2620178129498912010460166002268175319783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-97948990154849373734466732949756094000000000000000)
      constant := (748775168705518653090053431861931527951913691463232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree026.table
  base := (-10484511019074776346792157507473545186653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-48985576051671651674065516194320922000000000000000)
      constant := (374561716078695883402024744138328076313510129597464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7800220702951440213/3125000000000000000)
  centralHi := (249607062494446086817/100000000000000000000)
  directionLo := (254550256477950866183/100000000000000000000)
  directionHi := (31818782059743858273/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree027.table
  base := (-11043257365107009995316333631136142399003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-101169394033460348810519155874488009000000000000000)
      constant := (800205121067325510099995780242483612705641211368528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree027.table
  base := (-276168863544622004718658218646837490039/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-10119240836458866033240131298410013400000000000000)
      constant := (80057982501000113112178345153510307962399524475456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254550256477950866183/100000000000000000000)
  centralHi := (31818782059743858273/12500000000000000000)
  directionLo := (259399268501040340707/100000000000000000000)
  directionHi := (64849817125260085177/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree028.table
  base := (-2303449272656226291037927572440710924513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-20877959582414264777314315759843984800000000000000)
      constant := (170702452997538580935020440232517588243738986338288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree028.table
  base := (-2304092636648509274747697221067052369111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-10441366462583401731667159357955842400000000000000)
      constant := (85391426750107311586335986414677339367861911645768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259399268501040340707/100000000000000000000)
  centralHi := (64849817125260085177/25000000000000000000)
  directionLo := (264159285138264772789/100000000000000000000)
  directionHi := (26415928513826477279/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree029.table
  base := (-5954549658691825870323072456858591318121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-107610201790682298962624001723951839000000000000000)
      constant := (908683754746365211744722213715082736315120441594592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree029.table
  base := (-2978013942515282251737103800872859741543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-53817460443539687150470937087508357000000000000000)
      constant := (454556957933893895194630673116068081578626731151136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264159285138264772789/100000000000000000000)
  centralHi := (26415928513826477279/10000000000000000000)
  directionLo := (268835033711462771163/100000000000000000000)
  directionHi := (67208758427865692791/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree030.table
  base := (-12224465239607249566953389962486477382523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-110830605669293274038676424648683754000000000000000)
      constant := (965708286942091692594095266739946964631105857428048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree030.table
  base := (-2445436058234759734976436977431879928277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-11085617714832473128521215477047500400000000000000)
      constant := (96616746875638739520031542954508259760882573836376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268835033711462771163/100000000000000000000)
  centralHi := (67208758427865692791/25000000000000000000)
  directionLo := (136715418640809838621/50000000000000000000)
  directionHi := (273430837281619677243/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree031.table
  base := (-12468319065828920504947794741680427918601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-114051009547904249114728847573415669000000000000000)
      constant := (1024575906967854989896116300964562896212424805521776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree031.table
  base := (-2494162127356312311167335594705615048413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-11407743340957008826948243536593329400000000000000)
      constant := (102506497365220185125742369719904424625418079672344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136715418640809838621/50000000000000000000)
  centralHi := (273430837281619677243/100000000000000000000)
  directionLo := (138975330726726307889/50000000000000000000)
  directionHi := (277950661453452615779/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree032.table
  base := (-12645045455397203080563319854778606395153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-117271413426515224190781270498147584000000000000000)
      constant := (1085277841331534026835583486615853940417440539890928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree032.table
  base := (-2529466083346067351323055784488480005103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-11729868967081544525375271596139158400000000000000)
      constant := (108579765916311426236487146624972113313400811421064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138975330726726307889/50000000000000000000)
  centralHi := (277950661453452615779/100000000000000000000)
  directionLo := (70599538608750872963/25000000000000000000)
  directionHi := (282398154435003491853/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree033.table
  base := (-6379255796053288044442658000522764975873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-120491817305126199266833693422879499000000000000000)
      constant := (1147806351984661497826341468976447086217257209315296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree033.table
  base := (-12760605776311525370188814647826764975929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-60259972966030401119011498278424937000000000000000)
      constant := (574178894659325975247081583502453978555197775677752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70599538608750872963/25000000000000000000)
  centralHi := (282398154435003491853/100000000000000000000)
  directionLo := (286776681503535665221/100000000000000000000)
  directionHi := (143388340751767832611/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree034.table
  base := (-12812130556810051018745556171291816561659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-123712221183737174342886116347611414000000000000000)
      constant := (1212154609516879110053919356251225892339675015483984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree034.table
  base := (-6407024390182908110598252792869816075853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-61870601096653079611146638576154082000000000000000)
      constant := (606369268370724166536110267595567731578477417294128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286776681503535665221/100000000000000000000)
  centralHi := (143388340751767832611/50000000000000000000)
  directionLo := (72772338700937987093/25000000000000000000)
  directionHi := (291089354803751948373/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree035.table
  base := (-12808916580384478504872937971241436981349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-126932625062348149418938539272343329000000000000000)
      constant := (1278316582597415872121380803030507746659038664469424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree035.table
  base := (-12810672674890340923428969921390543946893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-63481229227275758103281778873883227000000000000000)
      constant := (639466936035714644448830584898310523799056146258584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72772338700937987093/25000000000000000000)
  centralHi := (291089354803751948373/100000000000000000000)
  directionLo := (18458691201778436397/6250000000000000000)
  directionHi := (295339059228454982353/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree036.table
  base := (-6375766640500683375826558442607364986303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-130153028940959124494990962197075244000000000000000)
      constant := (1346286941454633065142329367173506263929646554266656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree036.table
  base := (-12753140130575977216377842852228540543093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-65091857357898436595416919171612372000000000000000)
      constant := (673469233716409597408744143270143226667720055524184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18458691201778436397/6250000000000000000)
  centralHi := (295339059228454982353/100000000000000000000)
  directionLo := (299528474993335304179/100000000000000000000)
  directionHi := (14976423749666765209/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree037.table
  base := (-316058395619289129785027492394468623891/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-26674686563914019914208677024361431800000000000000)
      constant := (283212194702921072391796994263214307042366268582528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree037.table
  base := (-3160951351943486787085176339398769968151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-66702485488521115087552059469341517000000000000000)
      constant := (708373806032037051096765912333365341900243669285152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299528474993335304179/100000000000000000000)
  centralHi := (14976423749666765209/5000000000000000000)
  directionLo := (75915024351951136527/25000000000000000000)
  directionHi := (303660097407804546109/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree038.table
  base := (-12483407813216623821849313316399647936021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-136593836698181074647095808046539074000000000000000)
      constant := (1487634509591067727928077719961756745474460944747696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree038.table
  base := (-390148476460014546648089362022779961639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-68313113619143793579687199767070662000000000000000)
      constant := (744178569251159719442029341461990575949324686727424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75915024351951136527/25000000000000000000)
  centralHi := (303660097407804546109/100000000000000000000)
  directionLo := (61547250851228634807/20000000000000000000)
  directionHi := (76934063564035793509/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree039.table
  base := (-12276593587793001308496506030116667403107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-139814240576792049723148230971270989000000000000000)
      constant := (1561003859245618783266297286863897682208201705082832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree039.table
  base := (-12277821173565451070298829655641045958473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-69923741749766472071822340064799807000000000000000)
      constant := (780881678970271466563642096932460105662562811197624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61547250851228634807/20000000000000000000)
  centralHi := (76934063564035793509/25000000000000000000)
  directionLo := (31175912113278394083/10000000000000000000)
  directionHi := (311759121132783940831/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree040.table
  base := (-2404705309234640815487748061903346136821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-28606928891080604959840130779200580800000000000000)
      constant := (327233150825641281777139006923750716635824666488496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree040.table
  base := (-6012323908588440423796341967370950476653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-71534369880389150563957480362528952000000000000000)
      constant := (818481501783516645678377995134163928159127510234928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31175912113278394083/10000000000000000000)
  centralHi := (311759121132783940831/100000000000000000000)
  directionLo := (315730735018575761943/100000000000000000000)
  directionHi := (39466341877321970243/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree041.table
  base := (-117256539838218162389844478150711992453/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-5850201933360559995010123072829392760000000000000)
      constant := (68524691930813235131333915587708997158459981662912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree041.table
  base := (-2931669437619938353412492480446389486591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-73144998011011829056092620660258097000000000000000)
      constant := (856976590429528844315278986337338306307682630016032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315730735018575761943/100000000000000000000)
  centralHi := (39466341877321970243/12500000000000000000)
  directionLo := (19978312896157543819/6250000000000000000)
  directionHi := (63930601267704140221/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree042.table
  base := (-2276851781018357072499094078452289085803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-29895090442524994990261099949093346800000000000000)
      constant := (358371184888418392216112981625819248281787194645328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree042.table
  base := (-71157458129599568682122438454643055583/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-14951125228326901509645552191597448400000000000000)
      constant := (179273132394154253681260601005453733836596204265728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19978312896157543819/6250000000000000000)
  centralHi := (63930601267704140221/20000000000000000000)
  directionLo := (323527729703558189591/100000000000000000000)
  directionHi := (40440966212944773699/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree043.table
  base := (-2200095837733243014491417559964574421567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-30539171218247190005471584534039729800000000000000)
      constant := (374475871160612642072390251666695127242031766411792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree043.table
  base := (-5500665856868531466743633283625988851043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-76366254272257186040362901255716387000000000000000)
      constant := (936647578620223349396594386250137195837201844847568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323527729703558189591/100000000000000000000)
  centralHi := (40440966212944773699/12500000000000000000)
  directionLo := (163678296753893780143/50000000000000000000)
  directionHi := (327356593507787560287/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree044.table
  base := (-1057532444113327993652722361337810654583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-31183251993969385020682069118986112800000000000000)
      constant := (390937114435820099161904281343833683081091024381216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree044.table
  base := (-2644025501454192702615579968964625918947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-77976882402879864532498041553445532000000000000000)
      constant := (977821330881348484355878152710440209752010648381344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163678296753893780143/50000000000000000000)
  centralHi := (327356593507787560287/100000000000000000000)
  directionLo := (2069632428292173603/625000000000000000)
  directionHi := (331141188526747776481/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree045.table
  base := (-1010969082854208482231242141066069956399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-31827332769691580035892553703932495800000000000000)
      constant := (407754556077022650832974152279994628938713640956448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree045.table
  base := (-505519989681247702117131336063610082599/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-15917502106700508604926636370234935400000000000000)
      constant := (203977204542252412554988514531327838162897480578848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2069632428292173603/625000000000000000)
  centralHi := (331141188526747776481/100000000000000000000)
  directionLo := (334883015640971803841/100000000000000000000)
  directionHi := (167441507820485901921/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree046.table
  base := (-4802187068948804459086774615757645672003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-162357067727068875255515191444394394000000000000000)
      constant := (2124639388089642356823966603901339386626319782833056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree046.table
  base := (-1921004070739603584395100241539300227431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-16239627732825044303353664429780764400000000000000)
      constant := (212568171690989206473444920486716149971119162857928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334883015640971803841/100000000000000000000)
  centralHi := (167441507820485901921/50000000000000000000)
  directionLo := (338583492791180855561/100000000000000000000)
  directionHi := (169291746395590427781/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree047.table
  base := (-9060081287835969238945196167762679957487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-165577471605679850331567614369126309000000000000000)
      constant := (2212283980782553445853698228121697811821188144893712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree047.table
  base := (-1812134026225208724115622660067432389323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-16561753358949580001780692489326593400000000000000)
      constant := (221337026266220923250159343154053329211293732512424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338583492791180855561/100000000000000000000)
  centralHi := (169291746395590427781/50000000000000000000)
  directionLo := (171121980628264023549/50000000000000000000)
  directionHi := (342243961256528047099/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree048.table
  base := (-1059680059929629085381346500393905455853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-168797875484290825407620037293858224000000000000000)
      constant := (2301705301463749922813988089529957657277019105393024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree048.table
  base := (-8477976888320757205892441508265248576803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-84419394925370578501038602744362112000000000000000)
      constant := (1151418213278566423468540582937149605892216316530664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171121980628264023549/50000000000000000000)
  centralHi := (342243961256528047099/100000000000000000000)
  directionLo := (86466422833680113569/25000000000000000000)
  directionHi := (345865691334720454277/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree049.table
  base := (-7857010153652417002147150623186110080983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-172018279362901800483672460218590139000000000000000)
      constant := (2392902232719791051868907587302779470623242278437008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree049.table
  base := (-7857498660398630251436125005310881503691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-86030023055993256993173743042091257000000000000000)
      constant := (1197039545996639374096719068833705013046570815408808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/25000000000000000000)
  centralHi := (345865691334720454277/100000000000000000000)
  directionLo := (174724943746112260771/50000000000000000000)
  directionHi := (349449887492224521543/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree050.table
  base := (-287971476024768811154651699831731000273/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-7009547329660511022388995325732882160000000000000)
      constant := (99434951235909449047997895896846833486926396152048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree050.table
  base := (-1439946332495441284941611330195274344169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-17528130237323187097061776667964080400000000000000)
      constant := (248709726606810239089478278773466401012427317842872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174724943746112260771/50000000000000000000)
  centralHi := (349449887492224521543/100000000000000000000)
  directionLo := (22062355815234647801/6250000000000000000)
  directionHi := (352997693043754364817/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree051.table
  base := (-813089055967237650378923121871934572833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-178459087120123750635777306068053969000000000000000)
      constant := (2580619062122337787213269162911646244307899182420864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree051.table
  base := (-1626279318945984345391869912200023469273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-89251279317238613977444023637549547000000000000000)
      constant := (1290945032799515813145725871550340724935130765392096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22062355815234647801/6250000000000000000)
  centralHi := (352997693043754364817/100000000000000000000)
  directionLo := (14260407776503272559/4000000000000000000)
  directionHi := (44563774301572726747/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree052.table
  base := (-5773679837427239093046482132324640499003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-181679490998734725711829728992785884000000000000000)
      constant := (2677137289934650969059858815010659201733375676968528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree052.table
  base := (-5774048223505772590807823437709726362883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-90861907447861292469579163935278692000000000000000)
      constant := (1339228352382944600375433480025212355325824187625704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14260407776503272559/4000000000000000000)
  centralHi := (44563774301572726747/12500000000000000000)
  directionLo := (359988425016667909289/100000000000000000000)
  directionHi := (35998842501666790929/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree053.table
  base := (-200261555663875946985278186301778138987/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15101523200000000000000000000000000000000000000
      center := (99647915)
      previous := (0)
      next := (89121125)
      square := (2302115018938657714789997097793600000000000000)
      linear := (-139547090473468453424816718428315320000000000000)
      constant := (2094662463666330228636647334545427154332087487504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree053.table
  base := (-312929627089431385833789094157695480589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 188769040000000000000000000000000000000000000000
      center := (1245928625)
      previous := (0)
      next := (1113684375)
      square := (28776437736733221434874963722420000000000000000)
      linear := (-1744764822235546621919137815717129000000000000000)
      constant := (26196193246984998080801242614179238857327001336704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359988425016667909289/100000000000000000000)
  centralHi := (35998842501666790929/10000000000000000000)
  directionLo := (181716684410007730583/50000000000000000000)
  directionHi := (363433368820015461167/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree054.table
  base := (-420360104781307127757233877950006475389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-37624059751191335172786914968449942800000000000000)
      constant := (575097972444096281240460103880719955149517138680928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree054.table
  base := (-2101952936182729323550014787164247721357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-94083163709106649453849444530736982000000000000000)
      constant := (1438454390606402557308749988335908800984362867094832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181716684410007730583/50000000000000000000)
  centralHi := (363433368820015461167/100000000000000000000)
  directionLo := (366845963583831243677/100000000000000000000)
  directionHi := (183422981791915621839/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree055.table
  base := (-3365143641629745856317808048058395258179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-191340702634567650939986997766981629000000000000000)
      constant := (2977323028587349914587204290721662820130883779031504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree055.table
  base := (-42067760335028259615092322719025952689/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-19138758367945865589196916965693225400000000000000)
      constant := (297879304142635194345360836013207676856208861962112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366845963583831243677/100000000000000000000)
  centralHi := (183422981791915621839/50000000000000000000)
  directionLo := (370227103847940732513/100000000000000000000)
  directionHi := (185113551923970366257/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree056.table
  base := (-2491413700406724072491333793945129190833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-194561106513178626016039420691713544000000000000000)
      constant := (3080926769168646905059166316942364847589687064570608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree056.table
  base := (-2491665695165037674688297566281458637521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-97304419970352006438119725126195272000000000000000)
      constant := (1541224385494647080967822722106778749220935900105848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370227103847940732513/100000000000000000000)
  centralHi := (185113551923970366257/50000000000000000000)
  directionLo := (74715528733863121641/20000000000000000000)
  directionHi := (186788821834657804103/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree057.table
  base := (-12364307077768674714675091823570793601/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-197781510391789601092091843616445459000000000000000)
      constant := (3186300643591272459656058876581098601178171794787328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree057.table
  base := (-791430174484374349287784282536346916293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-98915048100974684930254865423924417000000000000000)
      constant := (1593937764974661433269445756581968208354046746331568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74715528733863121641/20000000000000000000)
  centralHi := (186788821834657804103/50000000000000000000)
  directionLo := (376898399141469419819/100000000000000000000)
  directionHi := (18844919957073470991/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree058.table
  base := (-63899257637856878894597850196967565363/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-40200382854080115233628853308235474800000000000000)
      constant := (658688851886469002060133665612926816006636131855776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree058.table
  base := (-6392007132686098720738747693616293763/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400190364800000000000000000000000000000000000000
      center := (2641368685)
      previous := (0)
      next := (2361010875)
      square := (61006048001874429441934923091530400000000000000)
      linear := (-4021027049263894536895600228866142480000000000000)
      constant := (65901458525396829108899870594255903857677610652576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376898399141469419819/100000000000000000000)
  centralHi := (18844919957073470991/5000000000000000000)
  directionLo := (380190150715778865859/100000000000000000000)
  directionHi := (19009507535788943293/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree059.table
  base := (339327688587775109281662627530779070021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-204222318149011551244196689465909289000000000000000)
      constant := (3402357266926020044879152183351543283027549543668304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree059.table
  base := (67827717863428390321036023560627550109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-20427260872444008382905029203876541400000000000000)
      constant := (340404061053940345596685371517255358247987627474408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380190150715778865859/100000000000000000000)
  centralHi := (19009507535788943293/5000000000000000000)
  directionLo := (11982926416982428163/3125000000000000000)
  directionHi := (383453645343437701217/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree060.table
  base := (1352173659801519342374175581112428327717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-207442722027622526320249112390641204000000000000000)
      constant := (3513039354265689401090905873888098225911414600905808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree060.table
  base := (676000946024377991502255145946787789843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-103746932492842720406660286317111852000000000000000)
      constant := (1757389135638181013814501236866458356235027279523632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11982926416982428163/3125000000000000000)
  centralHi := (383453645343437701217/100000000000000000000)
  directionLo := (193344799227348726231/50000000000000000000)
  directionHi := (386689598454697452463/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree061.table
  base := (2399406394168560236501455650089862071969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-210663125906233501396301535315373119000000000000000)
      constant := (3625490243432915499986133950591343848808064789821456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree061.table
  base := (2399250400667267894091438218145247749883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-105357560623465398898795426614840997000000000000000)
      constant := (1813642815380045767515455942474546930253530142318296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193344799227348726231/50000000000000000000)
  centralHi := (386689598454697452463/100000000000000000000)
  directionLo := (15595947831610076631/4000000000000000000)
  directionHi := (761520890215335773/195312500000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree062.table
  base := (3480901983118687984651182706646901106787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-213883529784844476472353958240105034000000000000000)
      constant := (3739709686492618771019432423511054454818573066429488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree062.table
  base := (3480760342934502144544515349333390313879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-106968188754088077390930566912570142000000000000000)
      constant := (1870781220664153120131371780402096742516330058782648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15595947831610076631/4000000000000000000)
  centralHi := (761520890215335773/195312500000000000)
  directionLo := (393081595098045336557/100000000000000000000)
  directionHi := (196540797549022668279/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree063.table
  base := (4596549907446389393780760738225949545611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-217103933663455451548406381164836949000000000000000)
      constant := (3855697462301193355536326646046207795548672301644464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree063.table
  base := (574552665558080764026946887176780175707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-108578816884710755883065707210299287000000000000000)
      constant := (1928804241043579246099243952282806782074611848558272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393081595098045336557/100000000000000000000)
  centralHi := (196540797549022668279/50000000000000000000)
  directionLo := (396238927707397159183/100000000000000000000)
  directionHi := (24764932981712322449/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree064.table
  base := (35914072343786568125285461037252038119/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-44064867508413285324891760817913772800000000000000)
      constant := (794690674716101051162455598699298687923901778529792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree064.table
  base := (5746134867339454574813183639234280775593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-110189445015333434375200847508028432000000000000000)
      constant := (1987711777993539077168860793132669884040625474015816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396238927707397159183/100000000000000000000)
  centralHi := (24764932981712322449/6250000000000000000)
  directionLo := (199685649995556869453/50000000000000000000)
  directionHi := (399371299991113738907/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree065.table
  base := (6929919020503794739993577259107440438937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-223544741420677401700511227014300779000000000000000)
      constant := (4092977244316240439011567856536045576839512350771088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree065.table
  base := (6929813110754563148838252697675918773103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-111800073145956112867335987805757577000000000000000)
      constant := (2047503743611414237830060734856468319177458144994936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199685649995556869453/50000000000000000000)
  centralHi := (399371299991113738907/100000000000000000000)
  directionLo := (402479294725177654427/100000000000000000000)
  directionHi := (100619823681294413607/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree066.table
  base := (4073736874527497133190763519642195265429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-226765145299288376776563649939032694000000000000000)
      constant := (4214268917443915136203742061439998758012448643384992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree066.table
  base := (8147377655365599041495685182068685858437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-113410701276578791359471128103486722000000000000000)
      constant := (2108180059460549166510904115663285002780861260469544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402479294725177654427/100000000000000000000)
  centralHi := (100619823681294413607/25000000000000000000)
  directionLo := (25347717022165603043/6250000000000000000)
  directionHi := (405563472354649648689/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree067.table
  base := (4699422853647253735764967749325863332789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-229985549177899351852616072863764609000000000000000)
      constant := (4337328252790120989340879915376878839543487737114272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree067.table
  base := (939875853513191833408678824930857144751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-23004265881440293970321253680243173400000000000000)
      constant := (433948131108321108191552721395541515390172945475824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25347717022165603043/6250000000000000000)
  centralHi := (405563472354649648689/100000000000000000000)
  directionLo := (408624372173570824601/100000000000000000000)
  directionHi := (204312186086785412301/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree068.table
  base := (667748272982152206445083429729507682007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-233205953056510326928668495788496524000000000000000)
      constant := (4462155125240327017639838909802176512066942698092288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree068.table
  base := (10683893302329477389024814922556866491107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-116631957537824148343741408698945012000000000000000)
      constant := (2232185469377139696287996810638970091374552515714584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408624372173570824601/100000000000000000000)
  centralHi := (204312186086785412301/50000000000000000000)
  directionLo := (102915628356474962727/25000000000000000000)
  directionHi := (411662513425899850909/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree069.table
  base := (6001398956771585722212045945518005605707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-236426356935121302004720918713228439000000000000000)
      constant := (4588749423107862265649744961387158193914413292919136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree069.table
  base := (2400545242610877919206880692496418966039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-23648517133689365367175309799334831400000000000000)
      constant := (459102889039343710620968779107956996234281965552568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102915628356474962727/25000000000000000000)
  centralHi := (411662513425899850909/100000000000000000000)
  directionLo := (25917399770865613429/6250000000000000000)
  directionHi := (82935679266769962973/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree070.table
  base := (133552725129393534864675780116769503099/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-9585870432549291083230933665518414160000000000000)
      constant := (188684441867264514639188930280246325805854070810304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree070.table
  base := (1669400937749103235908528728088435529693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-119853213799069505328011689294403302000000000000000)
      constant := (2359727533211344372305438200280094866675782458040128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25917399770865613429/6250000000000000000)
  centralHi := (82935679266769962973/20000000000000000000)
  directionLo := (52209062882423979133/12500000000000000000)
  directionHi := (83534500611878366613/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree071.table
  base := (3685337918138793093471431532502210213691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-242867164692343252156825764562692269000000000000000)
      constant := (4847239906932533364234035347692545556025715744889536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree071.table
  base := (14741292736515214982829077255432260793131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-121463841929692183820146829592132447000000000000000)
      constant := (2424824688967241561005355549661879239133729580560472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52209062882423979133/12500000000000000000)
  centralHi := (83534500611878366613/20000000000000000000)
  directionLo := (84129059720831762717/20000000000000000000)
  directionHi := (210322649302079406793/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree072.table
  base := (8080497830827688716442316811007433549353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-246087568570954227232878187487424184000000000000000)
      constant := (4979135924361336591715856094990715592876273358739744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree072.table
  base := (16160942241284221888810966699664974589073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-123074470060314862312281969889861592000000000000000)
      constant := (2490805872770190815068918344847842629546459634909576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84129059720831762717/20000000000000000000)
  centralHi := (210322649302079406793/50000000000000000000)
  directionLo := (423597231652505237779/100000000000000000000)
  directionHi := (21179861582625261889/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree073.table
  base := (880708449948878985047813536106754278829/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-49861594489913040461786122082431219800000000000000)
      constant := (1022559805594345170681611517825324958888020768536384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree073.table
  base := (8807060292782543090325794822082164791021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-124685098190937540804417110187590737000000000000000)
      constant := (2557671049172595462230261103027374588178962048772304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423597231652505237779/100000000000000000000)
  centralHi := (21179861582625261889/5000000000000000000)
  directionLo := (26658045960128180369/6250000000000000000)
  directionHi := (85305747072410177181/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree074.table
  base := (9550419997701167609419248677761587611869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-252528376328176177384983033336888014000000000000000)
      constant := (5248229154355299796966488469223365918063210159198112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree074.table
  base := (1910079612630961668159784808266458889971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-25259145264312043859310450097063976400000000000000)
      constant := (525084037303269600992374283054766204043908487757104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26658045960128180369/6250000000000000000)
  centralHi := (85305747072410177181/20000000000000000000)
  directionLo := (107360057026413078153/25000000000000000000)
  directionHi := (429440228105652312613/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree075.table
  base := (20620980346281994291850375891678619435013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-255748780206787152461035456261619929000000000000000)
      constant := (5385426246875822080057263870031158717011541111813712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree075.table
  base := (20620940600865480553908477284791879298741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-127906354452182897788687390783049027000000000000000)
      constant := (2694053256525345575028982541736057690734101822426792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107360057026413078153/25000000000000000000)
  centralHi := (429440228105652312613/100000000000000000000)
  directionLo := (86466422833680113569/20000000000000000000)
  directionHi := (216166057084200283923/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree076.table
  base := (11087282383983845989291031477079387850121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-258969184085398127537087879186351844000000000000000)
      constant := (5524390254941929389000340112314355967123006107141408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree076.table
  base := (4434905752770530778248455616452838651461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-25903396516561115256164506216155634400000000000000)
      constant := (552714046788438713845463193718598803354809294107432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86466422833680113569/20000000000000000000)
  centralHi := (216166057084200283923/50000000000000000000)
  directionLo := (217602392201466385667/50000000000000000000)
  directionHi := (87040956880586554267/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree077.table
  base := (46409317722040751157935561008500962719/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-262189587964009102613140302111083759000000000000000)
      constant := (5665121133358573962311070067860908502330719593321472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree077.table
  base := (23761538063359754391261644466104803605523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-131127610713428254772957671378507317000000000000000)
      constant := (2833971096204247880004759819740912327037316511661976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217602392201466385667/50000000000000000000)
  centralHi := (87040956880586554267/20000000000000000000)
  directionLo := (109514654211516211637/25000000000000000000)
  directionHi := (438058616846064846549/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree078.table
  base := (507639557688974307261598304825272154781/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-10616399673704803107567709001432626960000000000000)
      constant := (232304753669943174576840992225014180443810904541088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree078.table
  base := (25381948352153864171014112445219717006893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-132738238844050933265092811676236462000000000000000)
      constant := (2905255823154687279565946119515675698662853184461416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109514654211516211637/25000000000000000000)
  centralHi := (438058616846064846549/100000000000000000000)
  directionLo := (440893977299499636451/100000000000000000000)
  directionHi := (110223494324874909113/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree079.table
  base := (6758942092797593006506120040334876625293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-268630395721231052765245147960547589000000000000000)
      constant := (5951883344036647350353514656009169974098029971537728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree079.table
  base := (27035741630076625435746651656638096151349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-134348866974673611757227951973965607000000000000000)
      constant := (2977424396784786918751747021050127192163464580805288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440893977299499636451/100000000000000000000)
  centralHi := (110223494324874909113/25000000000000000000)
  directionLo := (88742243975427160327/20000000000000000000)
  directionHi := (110927804969283950409/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree080.table
  base := (28722926024689324214423895187267684547239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-271850799599842027841297570885279504000000000000000)
      constant := (6097914607989003756670934186321661414971054491213936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree080.table
  base := (14361450907112049094905262718666526314149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-135959495105296290249363092271694752000000000000000)
      constant := (3050476801003988810586622578499677144676040438557776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88742243975427160327/20000000000000000000)
  centralHi := (110927804969283950409/25000000000000000000)
  directionLo := (223255343760647869227/50000000000000000000)
  directionHi := (89302137504259147691/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree081.table
  base := (15221718225142231538965620725445724628193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-275071203478453002917349993810011419000000000000000)
      constant := (6245712604802625181757319186220810684096819010348064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree081.table
  base := (15221707266942235919720108058249915060547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-137570123235918968741498232569423897000000000000000)
      constant := (3124413021434741950277603974058475051850746590087728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223255343760647869227/50000000000000000000)
  centralHi := (89302137504259147691/20000000000000000000)
  directionLo := (449292712490002956269/100000000000000000000)
  directionHi := (44929271249000295627/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree082.table
  base := (16098643392335132381849684234476266420519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-278291607357063977993402416734743334000000000000000)
      constant := (6395277308738656974990039642353939669082694888153312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree082.table
  base := (16098633473770908321345495223299486776539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-139180751366541647233633372867153042000000000000000)
      constant := (3199233045229418976553591126077092155613779592457136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449292712490002956269/100000000000000000000)
  centralHi := (44929271249000295627/10000000000000000000)
  directionLo := (452057616817268892519/100000000000000000000)
  directionHi := (11301440420431722313/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree083.table
  base := (33984465532381285890447024744057462632707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-281512011235674953069454839659475249000000000000000)
      constant := (6546608696795226589706352107080336169546976913707568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree083.table
  base := (33984447579550569264060945589835039090223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-140791379497164325725768513164882187000000000000000)
      constant := (3274936860906912928647744006336149671225846506208376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452057616817268892519/100000000000000000000)
  centralHi := (11301440420431722313/2500000000000000000)
  directionLo := (113701428187048557519/25000000000000000000)
  directionHi := (454805712748194230077/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree084.table
  base := (3580496241983150722739382497099391847233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-56946483022857185629101452516841432800000000000000)
      constant := (1339941349683076668341105498296022559352023201405984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree084.table
  base := (35804946174348703383561579839898165605477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-142402007627787004217903653462611332000000000000000)
      constant := (3351524458206781035205004114761513684221266633770024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113701428187048557519/25000000000000000000)
  centralHi := (454805712748194230077/100000000000000000000)
  directionLo := (228768651575274412739/50000000000000000000)
  directionHi := (457537303150548825479/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree085.table
  base := (37658768265008990232382447274326527293829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-287952818992896903221559685508939079000000000000000)
      constant := (6854571445226363694571860201451662040191422921494096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree085.table
  base := (4707344195788920007814877825933174556587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-144012635758409682710038793760340477000000000000000)
      constant := (3428995827959036406428830358604761332086952595458752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228768651575274412739/50000000000000000000)
  centralHi := (457537303150548825479/100000000000000000000)
  directionLo := (14382896309511435963/3125000000000000000)
  directionHi := (460252681904365950817/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree086.table
  base := (39545874861134166837542787911270211282223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-291173222871507878297612108433670994000000000000000)
      constant := (7011202770806797102414013397115788871547029490624752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree086.table
  base := (19772930781777235063979363419726376617613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-145623263889032361202173934058069622000000000000000)
      constant := (3507350961967896357215119942150171509123923682876112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14382896309511435963/3125000000000000000)
  centralHi := (460252681904365950817/100000000000000000000)
  directionLo := (231476067135484722301/50000000000000000000)
  directionHi := (462952134270969444603/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree087.table
  base := (20733137436387418184942465324146724273451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-294393626750118853373664531358402909000000000000000)
      constant := (7169600710478837123467033878051401182138423706449248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree087.table
  base := (4146626284418256245970952932891093642191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-29446778403931007938861814871159753400000000000000)
      constant := (717317970581596167705249991858434154029196884806384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231476067135484722301/50000000000000000000)
  centralHi := (462952134270969444603/100000000000000000000)
  directionLo := (232817968621372722163/50000000000000000000)
  directionHi := (465635937242745444327/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree088.table
  base := (5427495217884402140842595797909370335803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-297614030628729828449716954283134824000000000000000)
      constant := (7329765251122531221628022065683978401680932042837376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree088.table
  base := (21709975431819569935756662562582152605789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-148844520150277718186444214653527912000000000000000)
      constant := (3666712494231618720204273398612840188406399852509136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232817968621372722163/50000000000000000000)
  centralHi := (465635937242745444327/100000000000000000000)
  directionLo := (234152179937436321573/50000000000000000000)
  directionHi := (468304359874872643147/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree089.table
  base := (2270346480545125518468169782583591005873/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-60166886901468160705153875441573347800000000000000)
      constant := (1498339276202007006510891490411119744778936296249408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree089.table
  base := (45406919771964034481436855878218787780479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-150455148280900396678579354951257057000000000000000)
      constant := (3747718880086065768123839975141337829702709183321848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234152179937436321573/50000000000000000000)
  centralHi := (468304359874872643147/100000000000000000000)
  directionLo := (470957663600135589777/100000000000000000000)
  directionHi := (235478831800067794889/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree090.table
  base := (47427173236844428830792458498299668903503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-304054838385951778601821800132598654000000000000000)
      constant := (7655394089657536983351503729978239461516060407839472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree090.table
  base := (47427164339892074269227609803350251222731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-152065776411523075170714495248986202000000000000000)
      constant := (3829609005239568140218150674679551069497490912355672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470957663600135589777/100000000000000000000)
  centralHi := (235478831800067794889/50000000000000000000)
  directionLo := (94719220505572728583/20000000000000000000)
  directionHi := (118399025631965910729/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree091.table
  base := (1979227517484273240214612007518752657297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-12291009690582510147114968922293222760000000000000)
      constant := (312834334707719625733315644165233622485073279059728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree091.table
  base := (12370169973210753096256362853089178643853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-153676404542145753662849635546715347000000000000000)
      constant := (3912382865015320900802906551102477465646659013475744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94719220505572728583/20000000000000000000)
  centralHi := (118399025631965910729/25000000000000000000)
  directionLo := (476219923727963091399/100000000000000000000)
  directionHi := (2381099618639815457/500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree092.table
  base := (51567469524463588766231819516462529121709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-310495646143173728753926645982062484000000000000000)
      constant := (7988089206737958253922741161134239956173736741547216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree092.table
  base := (6445932781494449086250518087032458068649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-155287032672768432154984775844444492000000000000000)
      constant := (3996040455232474023521149827329506999878666935063104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476219923727963091399/100000000000000000000)
  centralHi := (2381099618639815457/500000000000000000)
  directionLo := (59853670937617628087/12500000000000000000)
  directionHi := (478829367500941024697/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree093.table
  base := (53687514255502517784750454010745762280473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-313716050021784703829979068906794399000000000000000)
      constant := (8157086599302052376904834351115808220166632848932752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree093.table
  base := (53687507681410267233963122832640698094159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-156897660803391110647119916142173637000000000000000)
      constant := (4080581772153430039069975860686063678356570387398008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59853670937617628087/12500000000000000000)
  centralHi := (478829367500941024697/100000000000000000000)
  directionLo := (481424667634756216117/100000000000000000000)
  directionHi := (240712333817378108059/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree094.table
  base := (55840818783492874318348006171297485646259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-316936453900395678906031491831526314000000000000000)
      constant := (8327850538688626026150592248085366509475495764826416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree094.table
  base := (27920406420683350073716881485515009770907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-158508288934013789139255056439902782000000000000000)
      constant := (4166006812436759141485991717770439692630474183784368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481424667634756216117/100000000000000000000)
  centralHi := (240712333817378108059/50000000000000000000)
  directionLo := (242003025824637026333/50000000000000000000)
  directionHi := (484006051649274052667/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree095.table
  base := (29013690058136340865602687684830673145037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-320156857779006653982083914756258229000000000000000)
      constant := (8500381018910507236807127238906365538402669203394976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree095.table
  base := (29013687372957450508403938669334927616469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-160118917064636467631390196737631927000000000000000)
      constant := (4252315573095130309960231489710017960343581617989456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242003025824637026333/50000000000000000000)
  centralHi := (484006051649274052667/100000000000000000000)
  directionLo := (60821717628631118871/12500000000000000000)
  directionHi := (486573741029048950969/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree096.table
  base := (12049439115723796581425718040494817502217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-64675452331523525811627267536198028800000000000000)
      constant := (1734935606922940750645223443312288351743608230193808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree096.table
  base := (470681177542997001966594425806314340379/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-161729545195259146123525337035361072000000000000000)
      constant := (4339508051457721819426135101007638102406317881682944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60821717628631118871/12500000000000000000)
  centralHi := (486573741029048950969/100000000000000000000)
  directionLo := (489127951445108324903/100000000000000000000)
  directionHi := (61140993930638540613/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree097.table
  base := (62500262778621896254627935430440339509639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-326597665536228604134188760605722059000000000000000)
      constant := (8850741581015119134993446812465286503746241422631536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree097.table
  base := (31250129196683672371059515176745300261221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-163340173325881824615660477333090217000000000000000)
      constant := (4427584245136632278430474899078308339003617836417104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489127951445108324903/100000000000000000000)
  centralHi := (61140993930638540613/12500000000000000000)
  directionLo := (491668892966366644469/100000000000000000000)
  directionHi := (49166889296636664447/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree098.table
  base := (3239328978881743021458238349519207641017/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-65963613882967915842048236706090794800000000000000)
      constant := (1805714330766484928859086706868240217234310813460032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree098.table
  base := (16196643903881202784133939782957295865197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-164950801456504503107795617630819362000000000000000)
      constant := (4516544151996864824325078871584467822801147190538656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491668892966366644469/100000000000000000000)
  centralHi := (49166889296636664447/10000000000000000000)
  directionLo := (247098385130628055371/50000000000000000000)
  directionHi := (494196770261256110743/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree099.table
  base := (16776536015854844030136349661345696714009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-333038473293450554286293606455185889000000000000000)
      constant := (9208168249240323168014322583920131252069038459609664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree099.table
  base := (67106140483967616038500206602148404963949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-166561429587127181599930757928548507000000000000000)
      constant := (4606387770129503013620099377524230431178152202896488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247098385130628055371/50000000000000000000)
  centralHi := (494196770261256110743/100000000000000000000)
  directionLo := (496711782790121664721/100000000000000000000)
  directionHi := (248355891395060832361/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree100.table
  base := (69458954526143504992333279040786274580411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-336258877172061529362346029379917804000000000000000)
      constant := (9389531363817523370402365718108720479015838225119664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree100.table
  base := (34729475646349349907266862775704769062859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-168172057717749860092065898226277652000000000000000)
      constant := (4697115097827737882209413481594604985541826486704816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496711782790121664721/100000000000000000000)
  centralHi := (248355891395060832361/50000000000000000000)
  directionLo := (7800220702951440213/1562500000000000000)
  directionHi := (499214124988892173633/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree101.table
  base := (71845009436929910476815885742730169246627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-339479281050672504438398452304649719000000000000000)
      constant := (9572660994504815356182136665635286782925117001497648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree101.table
  base := (71845006516316749691864959657867079793103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-169782685848372538584201038524006797000000000000000)
      constant := (4788726133565442160530685512312116188193281495234936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7800220702951440213/1562500000000000000)
  centralHi := (499214124988892173633/100000000000000000000)
  directionLo := (100340797288901289641/20000000000000000000)
  directionHi := (250851993222253224103/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree102.table
  base := (37132153714340903213529188381297425249893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-342699684929283479514450875229381634000000000000000)
      constant := (9757557138566704317528388222413549947205554108309664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree102.table
  base := (74264304790875232005503984149158603865717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-171393313978995217076336178821735942000000000000000)
      constant := (4881220875978020196396195972219323348485199941108904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100340797288901289641/20000000000000000000)
  centralHi := (250851993222253224103/50000000000000000000)
  directionLo := (504181552062542013141/100000000000000000000)
  directionHi := (252090776031271006571/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree103.table
  base := (38358423639472123867223911130162116338577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-345920088807894454590503298154113549000000000000000)
      constant := (9944219793557116802268221468370065718988001699428896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree103.table
  base := (76716844896773772777725383590061387666527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-173003942109617895568471319119465087000000000000000)
      constant := (4974599323845291193375038958623093136024154152197624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504181552062542013141/100000000000000000000)
  centralHi := (252090776031271006571/50000000000000000000)
  directionLo := (253323501113733038051/50000000000000000000)
  directionHi := (506647002227466076103/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree104.table
  base := (3168105115783365378629075387059674993003/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-13965619707460217186662228843153818560000000000000)
      constant := (405305958291549845608616434226156642114096540087472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree104.table
  base := (79202625743465522636206500187296314928023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-174614570240240574060606459417194232000000000000000)
      constant := (5068861476076189297762713332909430719491853025281976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253323501113733038051/50000000000000000000)
  centralHi := (506647002227466076103/100000000000000000000)
  directionLo := (509100512955901732367/100000000000000000000)
  directionHi := (31818782059743858273/6250000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree105.table
  base := (81721648298095448161418963596124842645339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-352360896565116404742608144003577379000000000000000)
      constant := (10322844627805649880762489010579441699004154057148336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree105.table
  base := (81721646355787266542561980106047122343343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-176225198370863252552741599714923377000000000000000)
      constant := (5164007331695087202644838393193005600503931665053816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509100512955901732367/100000000000000000000)
  centralHi := (31818782059743858273/6250000000000000000)
  directionLo := (63942782005409741779/12500000000000000000)
  directionHi := (511542256043277934233/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree106.table
  base := (1316779806489951538977936265707622517209/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 377538080000000000000000000000000000000000000000
      center := (2491197875)
      previous := (0)
      next := (2228028125)
      square := (57552875473466442869749927444840000000000000000)
      linear := (-6709081140447686411672840885439798000000000000000)
      constant := (198392581195448177993066783235021567762675858039808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree106.table
  base := (84273905861739677586850948816442863360239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 188769040000000000000000000000000000000000000000
      center := (1245928625)
      previous := (0)
      next := (1113684375)
      square := (28776437736733221434874963722420000000000000000)
      linear := (-3355392952858225114054278113446274000000000000000)
      constant := (99245979053388124267317073606839010803136349020056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63942782005409741779/12500000000000000000)
  centralHi := (511542256043277934233/100000000000000000000)
  directionLo := (513972399204208992707/100000000000000000000)
  directionHi := (128493099801052248177/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree107.table
  base := (21714851266171900016762937459279357023713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-358801704322338354894712989853041209000000000000000)
      constant := (10708535482383951005402135104959598935679832954410048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree107.table
  base := (86859403481563536616917584934527927561901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-179446454632108609537011880310381667000000000000000)
      constant := (5356950149699509132409951894652594544179462839428712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513972399204208992707/100000000000000000000)
  centralHi := (128493099801052248177/25000000000000000000)
  directionLo := (516391106206928224409/100000000000000000000)
  directionHi := (51639110620692822441/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree108.table
  base := (89478139947062862716103619645379390133427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-362022108200949329970765412777773124000000000000000)
      constant := (10904030663482527867269172701931158148359488359020848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree108.table
  base := (1398095914343346649677251859573666729373/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-181057082762731288029147020608110812000000000000000)
      constant := (5454747110607286337181678086058305530744224599243264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516391106206928224409/100000000000000000000)
  centralHi := (51639110620692822441/10000000000000000000)
  directionLo := (259399268501040340707/50000000000000000000)
  directionHi := (103759707400416136283/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree109.table
  base := (11516263954670859756726898219063113546717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-365242512079560305046817835702505039000000000000000)
      constant := (11101292345403657402228592581506938709510629922894464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree109.table
  base := (92130110347431165764229593111559954372003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-182667710893353966521282160905839957000000000000000)
      constant := (5553427771929064991386296971055462517655508088691736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259399268501040340707/50000000000000000000)
  centralHi := (103759707400416136283/20000000000000000000)
  directionLo := (521194847846161589933/100000000000000000000)
  directionHi := (260597423923080794967/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree110.table
  base := (94815319576572210455933767434577600622131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-368462915958171280122870258627236954000000000000000)
      constant := (11300320527028752643302003763555530493759396559216944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree110.table
  base := (47407659206166551473932347925284227671013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-184278339023976645013417301203569102000000000000000)
      constant := (5652992133106978351614889684317772467326744734277712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521194847846161589933/100000000000000000000)
  centralHi := (260597423923080794967/50000000000000000000)
  directionLo := (52358019141987006907/10000000000000000000)
  directionHi := (523580191419870069071/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree111.table
  base := (97533763264747721996043515377297998549/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160076145920000000000000000000000000000000000000
      center := (1056267899)
      previous := (0)
      next := (944683925)
      square := (24402419200749771776773969236612160000000000000)
      linear := (-2973466558694258041591381452415750952000000000000)
      constant := (92008921658859803745449191012871814645355367227008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree111.table
  base := (97533762214039609247600082826893750128873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-185888967154599323505552441501298247000000000000000)
      constant := (5753440193642148721040528874027595508849784332207176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52358019141987006907/10000000000000000000)
  centralHi := (523580191419870069071/100000000000000000000)
  directionLo := (10519094338832636131/2000000000000000000)
  directionHi := (525954716941631806551/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree112.table
  base := (20057088450961405812128158728623232717481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-74980744743078646054995020895340156800000000000000)
      constant := (2340735277099045512417804821861481044114820083635344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree112.table
  base := (100285441306632427421147535548869498553623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-187499595285222001997687581799027392000000000000000)
      constant := (5854771953088445624571285629822626496134418651829176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10519094338832636131/2000000000000000000)
  centralHi := (525954716941631806551/100000000000000000000)
  directionLo := (264159285138264772789/50000000000000000000)
  directionHi := (528318570276529545579/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree113.table
  base := (51535178073459469167801455597411044530511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-378124127594004205351027527401432699000000000000000)
      constant := (11908004060641965969471639058060121848743392418204128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree113.table
  base := (51535177645668691010318802249926155859933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-189110223415844680489822722096756537000000000000000)
      constant := (5956987411046905105343904755740763675495741224867792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264159285138264772789/50000000000000000000)
  centralHi := (528318570276529545579/100000000000000000000)
  directionLo := (66333986755108300593/12500000000000000000)
  directionHi := (106134378808173280949/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree114.table
  base := (3309015768234676926906973924421810836553/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-381344531472615180427079950326164614000000000000000)
      constant := (12114098232082202766695838802928137416366078119125504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree114.table
  base := (105888503811537043302419517287076904090269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-190720851546467358981957862394485682000000000000000)
      constant := (6060086567160740015100511319062850775683848408100328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66333986755108300593/12500000000000000000)
  centralHi := (106134378808173280949/20000000000000000000)
  directionLo := (533014827702574136737/100000000000000000000)
  directionHi := (266507413851287068369/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree115.table
  base := (27184971811198517508644271644907793633567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-384564935351226155503132373250896529000000000000000)
      constant := (12321958899176063316596346894977880774462855905104832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree115.table
  base := (27184971637077865285944777448408314239373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-192331479677090037474093002692214827000000000000000)
      constant := (6164069421110878625887088354528704571110577153932704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533014827702574136737/100000000000000000000)
  centralHi := (266507413851287068369/50000000000000000000)
  directionLo := (535347507677666363451/100000000000000000000)
  directionHi := (133836876919416590863/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree116.table
  base := (22324900768955982468486402075145444866013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-77557067845967426115836959235125688800000000000000)
      constant := (2506317212270258180531414766784192242269940147957712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree116.table
  base := (55812251608225491447117182392542751562287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-193942107807712715966228142989943972000000000000000)
      constant := (6268935972611975550356941648706103119736537022261488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535347507677666363451/100000000000000000000)
  centralHi := (133836876919416590863/25000000000000000000)
  directionLo := (268835033711462771163/50000000000000000000)
  directionHi := (537670067422925542327/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree117.table
  base := (57271177063847439715525884511149864387489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-391005743108448105655237219100360359000000000000000)
      constant := (12742979718096097456348559528452885543998247514659872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree117.table
  base := (114542353560891116244995480917660394411159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-195552735938335394458363283287673117000000000000000)
      constant := (6374686221408844907948617739479336055567284003502008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268835033711462771163/50000000000000000000)
  centralHi := (537670067422925542327/100000000000000000000)
  directionLo := (269991318762500931967/50000000000000000000)
  directionHi := (107996527505000372787/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree118.table
  base := (117493437864791714930065773987595316027779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-394226146987059080731289642025092274000000000000000)
      constant := (12956139868952770737801515329895088381104640824718896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree118.table
  base := (117493437353524711800978806517883880800861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-197163364068958072950498423585402262000000000000000)
      constant := (6481320167273270990337350062124094102204340699360232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269991318762500931967/50000000000000000000)
  centralHi := (107996527505000372787/20000000000000000000)
  directionLo := (108457069157218480257/20000000000000000000)
  directionHi := (271142672893046200643/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree119.table
  base := (4819110194059653145253290275139612753329/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-15897862034626802232293682597992967560000000000000)
      constant := (526842660540478313732467977085230534864677324622096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree119.table
  base := (15059719298793935983041802537434450879899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-198773992199580751442633563883131407000000000000000)
      constant := (6588837810001156429643225308202357708136789235943104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108457069157218480257/20000000000000000000)
  centralHi := (271142672893046200643/50000000000000000000)
  directionLo := (272289158653179789181/50000000000000000000)
  directionHi := (544578317306359578363/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree120.table
  base := (123495304904828116757660318896336403421803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-400666954744281030883394487874556104000000000000000)
      constant := (13387759651407553414271880401612555723344456554218672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree120.table
  base := (123495304488929162469693081962016616898953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-200384620330203429934768704180860552000000000000000)
      constant := (6697239149409972117429579534607818064151134614520136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272289158653179789181/50000000000000000000)
  centralHi := (544578317306359578363/100000000000000000000)
  directionLo := (109372334912647870897/20000000000000000000)
  directionHi := (273430837281619677243/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree121.table
  base := (126546087861165490143863067391839360974027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-403887358622892005959446910799288019000000000000000)
      constant := (13606219282312128519118838903192967996837223742275248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree121.table
  base := (126546087486094248928567179838656692639341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-201995248460826108426903844478589697000000000000000)
      constant := (6806524185336476915546648238157381358485748374053992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109372334912647870897/20000000000000000000)
  centralHi := (273430837281619677243/50000000000000000000)
  directionLo := (109827107497556278199/20000000000000000000)
  directionHi := (137283884371945347749/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree122.table
  base := (25926020714830600885638815550586466712793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4001903648000000000000000000000000000000000000000
      center := (26406697475)
      previous := (0)
      next := (23617098125)
      square := (610060480018744294419349230915304000000000000000)
      linear := (-81421552500300596207099866744803986800000000000000)
      constant := (2765289081186568593852745581543801304063678437484432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree122.table
  base := (64815051617961979612248445756325255168307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-203605876591448786919038984776318842000000000000000)
      constant := (6916692917634678589572081107007296269116289318641968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109827107497556278199/20000000000000000000)
  centralHi := (137283884371945347749/25000000000000000000)
  directionLo := (27570001176907791981/5000000000000000000)
  directionHi := (551400023538155839621/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree123.table
  base := (4148354747278109964531067711383986869611/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-410328166380113956111551756648751849000000000000000)
      constant := (14048438022007789897886079952453611064947735779854848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree123.table
  base := (26549470321582737512408225909462484109437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000951824000000000000000000000000000000000000000
      center := (13206843425)
      previous := (0)
      next := (11805054375)
      square := (305030240009372147209674615457652000000000000000)
      linear := (-41043300944414293082234825014809597400000000000000)
      constant := (1405549069234802085000496746752414595731674490381544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27570001176907791981/5000000000000000000)
  centralHi := (551400023538155839621/100000000000000000000)
  directionLo := (69206905971306779081/12500000000000000000)
  directionHi := (553655247770454232649/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree124.table
  base := (135897832760339520756034986695503588358107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-413548570258724931187604179573483764000000000000000)
      constant := (14272197130302726853824879863437128466223699366837168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree124.table
  base := (135897832485347252610558694171118530594521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-206827132852694143903309265371777132000000000000000)
      constant := (7139681470837700693875925490535521928956653299678152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69206905971306779081/12500000000000000000)
  centralHi := (553655247770454232649/100000000000000000000)
  directionLo := (555901322906905231557/100000000000000000000)
  directionHi := (277950661453452615779/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree125.table
  base := (139081546011772175078566958837402413438457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-416768974137335906263656602498215679000000000000000)
      constant := (14497722730608152510267033789656197548122932645895568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree125.table
  base := (139081545763839495783429071732492282324693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-208437760983316822395444405669506277000000000000000)
      constant := (7252501291521314559456192587934173612754258709295016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555901322906905231557/100000000000000000000)
  centralHi := (277950661453452615779/50000000000000000000)
  directionLo := (139534589850404918267/25000000000000000000)
  directionHi := (558138359401619673069/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree126.table
  base := (5691939662942192972391995133425101295787/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800380729600000000000000000000000000000000000000
      center := (5281339495)
      previous := (0)
      next := (4723419625)
      square := (122012096003748858883869846183060800000000000000)
      linear := (-16799575120637875253588361016917903760000000000000)
      constant := (589000592909467696833524293965526398890189761165488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree126.table
  base := (35574622837508248717656243447549919523941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-210048389113939500887579545967235422000000000000000)
      constant := (7366204808131450169615738919009897387854965911236768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139534589850404918267/25000000000000000000)
  centralHi := (558138359401619673069/100000000000000000000)
  directionLo := (140091616375993353077/25000000000000000000)
  directionHi := (560366465503973412309/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree127.table
  base := (18193583670241824885088714379655025747647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-423209781894557856415761448347679509000000000000000)
      constant := (14954073406520761128808918179648661969365419826865024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree127.table
  base := (18193583645054073104822508229998487385881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-211659017244562179379714686264964567000000000000000)
      constant := (7480792020584572622970016694637053847470578315187776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140091616375993353077/25000000000000000000)
  centralHi := (560366465503973412309/100000000000000000000)
  directionLo := (562585747319730876281/100000000000000000000)
  directionHi := (281292873659865438141/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree128.table
  base := (74416039651001765291187231498412664717629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-426430185773168831491813871272411424000000000000000)
      constant := (15184898481810471397359118685917486341142880385010592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree128.table
  base := (18604009890045388130645443696942300066083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10004759120000000000000000000000000000000000000000
      center := (66034217125)
      previous := (0)
      next := (59025271875)
      square := (1525151200046860736048373077288260000000000000000)
      linear := (-213269645375184857871849826562693712000000000000000)
      constant := (7596262928805971220071843598756840890159936397541568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell130.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562585747319730876281/100000000000000000000)
  centralHi := (281292873659865438141/50000000000000000000)
  directionLo := (112959261774001396741/20000000000000000000)
  directionHi := (282398154435003491853/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 94453
  qDenominator := 178928
  table := BinomialMassData.Q94453_178928.Degree129.table
  base := (19018590165845512803867363407821214251891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20009518240000000000000000000000000000000000000000
      center := (132033487375)
      previous := (0)
      next := (118085490625)
      square := (3050302400093721472096746154576520000000000000000)
      linear := (-429650589651779806567866294197143339000000000000000)
      constant := (15417490048471764423876963891434890415466978735193472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94453_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree129.table
  base := (243437953860859738080490492045574946667/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80038072960000000000000000000000000000000000000
      center := (528273737)
      previous := (0)
      next := (472202175)
      square := (12201209600374885888386984618306080000000000000)
      linear := (-1719042188046460290911879734883382856000000000000)
      constant := (61700940261830615655136732638768296558155090926520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell130.Kernel129
