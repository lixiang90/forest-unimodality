import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell119.Parameters
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch000_049
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch050_099
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch100_149
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch150_199
import ForestUnimodality.BinomialMassData.Q11_21.Batch000_049
import ForestUnimodality.BinomialMassData.Q11_21.Batch050_099
import ForestUnimodality.BinomialMassData.Q11_21.Batch100_149
import ForestUnimodality.BinomialMassData.Q11_21.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree000.table
  base := (29173372160968741058525211/400000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-43654615535763047554085325000000000000)
      constant := (729334304024218526463130275000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree000.table
  base := (29173372160968741058525211/400000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-43654615535763047554085325000000000000)
      constant := (729334304024218526463130275000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree001.table
  base := (403111092047144941009563840703665177787879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-240357431580133938989187955895055000000000000)
      constant := (123324443723428043661554980383866142916666398193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree001.table
  base := (40275724103549829548046379623647447375507/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-2360665704959344452992797695000000000000)
      constant := (1208924292750952814287872474194423421265210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49943278484292930809/100000000000000000000)
  directionHi := (4994327848429293081/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree002.table
  base := (118440637417500766923335659701147949844357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-467366722331744218216905904220835000000000000)
      constant := (72682005968044102011036534665187845360119013638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree002.table
  base := (29565255162196468493672335093978800964781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-32132572943179798343263375905000000000000)
      constant := (4984274415752041899592232812218438562083208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/100000000000000000000)
  centralHi := (4994327848429293081/10000000000000000000)
  directionLo := (35315230890931728327/50000000000000000000)
  directionHi := (14126092356372691331/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree003.table
  base := (74710288594113380016518940926380993565749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-694376013083354497444623852546615000000000000)
      constant := (46243345917477066317395029546705922019236748966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree003.table
  base := (7456943753344749431847535811237760510947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-15913495317214728505192389315000000000000)
      constant := (1056715686460094618188567931608286471532580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35315230890931728327/50000000000000000000)
  centralHi := (14126092356372691331/20000000000000000000)
  directionLo := (43252147915678452363/50000000000000000000)
  directionHi := (86504295831356904727/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree004.table
  base := (50627868276134794208592229564600125982157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-921385303834964776672341800872395000000000000)
      constant := (31938842500209531438536164560165963442372398838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree004.table
  base := (101051025451879304769042399822551263214929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-63348398960108572687890959985000000000000)
      constant := (2189396925418032596678632707693576527513509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43252147915678452363/50000000000000000000)
  centralHi := (86504295831356904727/100000000000000000000)
  directionLo := (49943278484292930809/50000000000000000000)
  directionHi := (99886556968585861619/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree005.table
  base := (36552010117708856028943938745511931319463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-1148394594586575055900059749198175000000000000)
      constant := (23872472389294700417962953540429955907516486242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree005.table
  base := (2918271319861574358210142122403076019839/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-78956311968572959860204752025000000000000)
      constant := (1636688115289596040732615802636614910415475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/50000000000000000000)
  centralHi := (99886556968585861619/100000000000000000000)
  directionLo := (111676565710081656061/100000000000000000000)
  directionHi := (55838282855040828031/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree006.table
  base := (5546096316250963768467192183644646201657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-196486269334026476446825385360565000000000000)
      constant := (2734011973156524134691670803495712907345794170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree006.table
  base := (13838157565775218637677913881906901034669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-31521408325679115677506181355000000000000)
      constant := (437482254267238125728443383683393228970732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/100000000000000000000)
  centralHi := (55838282855040828031/50000000000000000000)
  directionLo := (122335548368239324001/100000000000000000000)
  directionHi := (61167774184119662001/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree007.table
  base := (43580463217306515717401197197778830340433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-228916168012827944907927949407105000000000000)
      constant := (2326353623262347527657590214171519588100453873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree007.table
  base := (43497690814134502062914328121268068986839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-15738876855071676314976048015000000000000)
      constant := (159587780395481609527746541678804206960517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/100000000000000000000)
  centralHi := (61167774184119662001/50000000000000000000)
  directionLo := (26427498905736396089/20000000000000000000)
  directionHi := (66068747264340990223/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree008.table
  base := (35041876149445339436421743400134120303827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-1829422466841405893583213594175515000000000000)
      constant := (14571493911016246194598828723827269562940270309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree008.table
  base := (8744019015800378965091159199270273885531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-17968578713423731625306589735000000000000)
      constant := (142851079267764781571123872831243286626372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/20000000000000000000)
  centralHi := (66068747264340990223/50000000000000000000)
  directionLo := (35315230890931728327/25000000000000000000)
  directionHi := (141260923563726913309/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree009.table
  base := (5714335918306472196075603100207654812581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-2056431757593016172810931542501295000000000000)
      constant := (13609738342924225343505686387924422445392273135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree009.table
  base := (28517596427787660920825431365840088043863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-47129321334143502849819973395000000000000)
      constant := (311434019295620544876424650425880616307041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35315230890931728327/25000000000000000000)
  centralHi := (141260923563726913309/100000000000000000000)
  directionLo := (149829835452878792427/100000000000000000000)
  directionHi := (37457458863219698107/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree010.table
  base := (23470331085532429827261834069187223773027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-2283441048344626452038649490827075000000000000)
      constant := (13185311659794336270660829491320544851407146709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree010.table
  base := (11712398188553033730061060152842146014387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-156995877010894895721773712225000000000000)
      constant := (905501405659371492120779894169370132604254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149829835452878792427/100000000000000000000)
  centralHi := (37457458863219698107/25000000000000000000)
  directionLo := (78967256913223805931/50000000000000000000)
  directionHi := (157934513826447611863/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree011.table
  base := (19331801930976780467240359919757560345691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-20747523463605262241870805282255000000000000)
      constant := (108876559371655751672885952851154854993561157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree011.table
  base := (4823218752135240478512350038781718286981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-172603790019359282894087504265000000000000)
      constant := (905054779236951798624073565802664336106404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78967256913223805931/50000000000000000000)
  centralHi := (157934513826447611863/100000000000000000000)
  directionLo := (8282155776631469679/5000000000000000000)
  directionHi := (165643115532629393581/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree012.table
  base := (7952517252929275423504006074577475615401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-2737459629847847010494085387478635000000000000)
      constant := (13499229279544082199327711242782671972988635134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree012.table
  base := (3967867823952312926332542971290562883461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-62737234342607890022133765435000000000000)
      constant := (309234865689219203338778628856135760736908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8282155776631469679/5000000000000000000)
  centralHi := (165643115532629393581/100000000000000000000)
  directionLo := (43252147915678452363/25000000000000000000)
  directionHi := (173008591662713809453/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree013.table
  base := (2604896634636991921157415790253837331941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-423495560085636755674543333686345000000000000)
      constant := (2015741436247024747577920532697206842482574105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree013.table
  base := (12995428612312355234841257806042948918967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-203819616036288057238715088345000000000000)
      constant := (969982569992918712715980124981901927298307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43252147915678452363/25000000000000000000)
  centralHi := (173008591662713809453/100000000000000000000)
  directionLo := (22509131429986948829/12500000000000000000)
  directionHi := (180073051439895590633/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree014.table
  base := (1057449213894803642456526808001699868937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-455925458764438224135645897732885000000000000)
      constant := (2138797468765597713291280884296417519750370970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree014.table
  base := (2109862019197234770106515070044557198523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-31346789863536063487289840055000000000000)
      constant := (147066360558484147861422078160668357977845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22509131429986948829/12500000000000000000)
  centralHi := (180073051439895590633/100000000000000000000)
  directionLo := (1868706368604626997/1000000000000000000)
  directionHi := (186870636860462699701/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree015.table
  base := (8470412171925084484684133776671888777369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-3418487502102677848177239232455975000000000000)
      constant := (16057523020950844141157541642057570915789787023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree015.table
  base := (8448594665604312733349806206601824038029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-11192163907296039599206793925000000000000)
      constant := (52589310291014965988481831831601824038029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1868706368604626997/1000000000000000000)
  centralHi := (186870636860462699701/100000000000000000000)
  directionLo := (48357371456166430717/25000000000000000000)
  directionHi := (193429485824665722869/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree016.table
  base := (6648128036618485461371168373993581810073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-3645496792854288127404957180781755000000000000)
      constant := (17348407949291753415090454732939335529320590991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree016.table
  base := (103582000769454037573967092493748186137/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-250643355061681218755656464465000000000000)
      constant := (1193370826888338481850731703431597562168128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48357371456166430717/25000000000000000000)
  centralHi := (193429485824665722869/100000000000000000000)
  directionLo := (49943278484292930809/25000000000000000000)
  directionHi := (199773113937171723237/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree017.table
  base := (2528956652778390330339313527588411419351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-3872506083605898406632675129107535000000000000)
      constant := (18829032365833246304365385373320124088921394434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree017.table
  base := (2520800297081545216467404101431587017613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-266251268070145605927970256505000000000000)
      constant := (1295407393532809894241043616015126654739746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/25000000000000000000)
  centralHi := (199773113937171723237/100000000000000000000)
  directionLo := (41184282496075530003/20000000000000000000)
  directionHi := (6435044140011801563/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree018.table
  base := (3660589288507923958398996410962091245249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-4099515374357508685860393077433315000000000000)
      constant := (20487416719999140761721774810590880753786050983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree018.table
  base := (911629460493452695313412010083468313549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-93953060359536664366761349515000000000000)
      constant := (469887797472883988052792428292337112779372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41184282496075530003/20000000000000000000)
  centralHi := (6435044140011801563/3125000000000000000)
  directionLo := (211891385345590369963/100000000000000000000)
  directionHi := (52972846336397592491/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree019.table
  base := (2424968962467666017118756027731137575393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-11984832867338279681684518076895000000000000)
      constant := (61811703737746527645447931159115773526357871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree019.table
  base := (603212524162052850526201506726631375943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-297467094087074380272597840585000000000000)
      constant := (1535484679929255522603434954510037035579212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211891385345590369963/100000000000000000000)
  centralHi := (52972846336397592491/25000000000000000000)
  directionLo := (108848851911071053997/50000000000000000000)
  directionHi := (43539540764428421599/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree020.table
  base := (41439365306547739932402210500868407007/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-650504850837247034902261282012125000000000000)
      constant := (3471602204283739686601414409458679852367128544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree020.table
  base := (328909432802478202512284645950062820123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-313075007095538767444911632625000000000000)
      constant := (1672347103898116600381994609759805276890332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108848851911071053997/50000000000000000000)
  centralHi := (43539540764428421599/20000000000000000000)
  directionLo := (111676565710081656061/50000000000000000000)
  directionHi := (223353131420163312123/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree021.table
  base := (343743178606103631659544800730435985577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-682934749516048503363363846058665000000000000)
      constant := (3777548050315773971606691246194263674285988937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree021.table
  base := (83698066302307916831176898275888620461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-15651567624000150219867877365000000000000)
      constant := (86658514582656754638145502388103554481844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/50000000000000000000)
  centralHi := (223353131420163312123/100000000000000000000)
  directionLo := (228868854108531729137/100000000000000000000)
  directionHi := (114434427054265864569/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree022.table
  base := (-67278161205961262473030733765279230391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-41384731713751651262572436948235000000000000)
      constant := (237470419150050185556222676002986115078415544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree022.table
  base := (-545903951393359944873369250538444045811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-49184404730352505969934173815000000000000)
      constant := (282512745184493025337959321038384667862567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228868854108531729137/100000000000000000000)
  centralHi := (114434427054265864569/50000000000000000000)
  directionLo := (46850948099995593639/20000000000000000000)
  directionHi := (58563685124994492049/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree023.table
  base := (-66649614275452839078145549099728346739/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-5234561828115560081998982819062215000000000000)
      constant := (31170448737383577388628043654804464752053123740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree023.table
  base := (-1339572970837829794179781570367611223581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-359898746120931928961853008745000000000000)
      constant := (2145352770968055267155645219027280164304799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46850948099995593639/20000000000000000000)
  centralHi := (58563685124994492049/25000000000000000000)
  directionLo := (239519549332557937093/100000000000000000000)
  directionHi := (119759774666278968547/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree024.table
  base := (-2051215777653415167312621955091450723521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-5461571118867170361226700767387995000000000000)
      constant := (33749161557784955844179067072047492386621154393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree024.table
  base := (-102842534049907927409575268705971465527/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-125168886376465438711388933595000000000000)
      constant := (774298705540083507583769656421163994826220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239519549332557937093/100000000000000000000)
  centralHi := (119759774666278968547/50000000000000000000)
  directionLo := (122335548368239324001/50000000000000000000)
  directionHi := (244671096736478648003/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree025.table
  base := (-337693601019860136016862194589963939587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-5688580409618780640454418715713775000000000000)
      constant := (36467413363643108575627595959167296468674414168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree025.table
  base := (-2706370372649487914695694761935793576041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-391114572137860703306480592825000000000000)
      constant := (2510037954141758968289176261874348334903139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/50000000000000000000)
  centralHi := (244671096736478648003/100000000000000000000)
  directionLo := (49943278484292930809/20000000000000000000)
  directionHi := (124858196210732327023/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree026.table
  base := (-102844551637636077875560169685626332397/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-5915589700370390919682136664039555000000000000)
      constant := (39323053305678255482577126145108137983102928032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree026.table
  base := (-205946798215937205977988118248233571081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-406722485146325090478794384865000000000000)
      constant := (2706630932293653878328182433538593520116784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/20000000000000000000)
  centralHi := (124858196210732327023/50000000000000000000)
  directionLo := (254661751564208336051/100000000000000000000)
  directionHi := (63665437891052084013/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree027.table
  base := (-3825371388182274704825031231038062471147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-877514141588857314129979230337905000000000000)
      constant := (6044904406289862252810915161989218893197827893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree027.table
  base := (-957223864293839949271295906440067373039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-140776799384929825883702725635000000000000)
      constant := (970851716633653663880514498054678113554908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254661751564208336051/100000000000000000000)
  centralHi := (63665437891052084013/25000000000000000000)
  directionLo := (259512887494070714179/100000000000000000000)
  directionHi := (12975644374703535709/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree028.table
  base := (-861850153879490904945831375418007687823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-909944040267658782591081794384445000000000000)
      constant := (6491402807269748077438069999208260030941017685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree028.table
  base := (-4312261571742033167728073448589389557997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-62562615880464837831917424135000000000000)
      constant := (446816133283302831643733433794231831326009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259512887494070714179/100000000000000000000)
  centralHi := (12975644374703535709/5000000000000000000)
  directionLo := (26427498905736396089/10000000000000000000)
  directionHi := (264274989057363960891/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree029.table
  base := (-4746468719816526371746722693165692841581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-6596617572625221757365290509016895000000000000)
      constant := (48698356306130505904576216933172408096908302373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree029.table
  base := (-2374520069908942398088383222293814995799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-64792317738816893142247965855000000000000)
      constant := (478860661146030015823049718851237110025206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/10000000000000000000)
  centralHi := (264274989057363960891/100000000000000000000)
  directionLo := (134476392823266082781/50000000000000000000)
  directionHi := (268952785646532165563/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree030.table
  base := (-514013211346435181279205637301609931231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-6823626863376832036593008457342675000000000000)
      constant := (52088990830205884010474893714133111361572908230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree030.table
  base := (-514232767579466239494109182663594475577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-156384712393394213056016517675000000000000)
      constant := (1195141736072001719148159688963548386709610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134476392823266082781/50000000000000000000)
  centralHi := (268952785646532165563/100000000000000000000)
  directionLo := (5471012044321932057/2000000000000000000)
  directionHi := (273550602216096602851/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree031.table
  base := (-2746390246725717282764220971550696218863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-7050636154128442315820726405668455000000000000)
      constant := (55610946714636101469523770970421294038493834158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree031.table
  base := (-1373663683668954624582182032168785576739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-484762050188647026340363345065000000000000)
      constant := (3827861531909432458335065892142822011553924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5471012044321932057/2000000000000000000)
  centralHi := (273550602216096602851/100000000000000000000)
  directionLo := (69518101526935393233/25000000000000000000)
  directionHi := (278072406107741572933/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree032.table
  base := (-1451622954895739771202787550741229963411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-7277645444880052595048444353994235000000000000)
      constant := (59263588587885406446515117115472985351110835052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree032.table
  base := (-1452022875274803752005086000630671937839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-500369963197111413512677137105000000000000)
      constant := (4079290125225096913497814466027023557221524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69518101526935393233/25000000000000000000)
  centralHi := (278072406107741572933/100000000000000000000)
  directionLo := (282521847127453826617/100000000000000000000)
  directionHi := (141260923563726913309/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree033.table
  base := (-6082968110086425660838783393328565497249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-62021939963898040283274068614215000000000000)
      constant := (521044595280549015373684100313631214988451777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree033.table
  base := (-6084333284225450844568540307010487075407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-171992625401858600228330309715000000000000)
      constant := (1446558462223541981867040056835926590472151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282521847127453826617/100000000000000000000)
  centralHi := (141260923563726913309/50000000000000000000)
  directionLo := (286902292026515583239/100000000000000000000)
  directionHi := (7172557300662889581/2500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree034.table
  base := (-1580901218510122562475994329352939127789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1104523432340467593357697178663685000000000000)
      constant := (9565563191027817330691145380886782063836194764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree034.table
  base := (-6324769816279785373545467800092727388459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-531585789214040187857304721185000000000000)
      constant := (4608988131869289107967967839668052724842361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286902292026515583239/100000000000000000000)
  centralHi := (7172557300662889581/2500000000000000000)
  directionLo := (72804213578193597743/25000000000000000000)
  directionHi := (291216854312774390973/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree035.table
  base := (-6529547461007854001422096915399423997943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1136953331019269061818799742710225000000000000)
      constant := (10142982471790077052575507686940250260345851817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree035.table
  base := (-3265270740795137128904102669287416577937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-78170528888929225004231216175000000000000)
      constant := (698172058964313890239765545359275500532378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72804213578193597743/25000000000000000000)
  centralHi := (291216854312774390973/100000000000000000000)
  directionLo := (59093684028527888553/20000000000000000000)
  directionHi := (147734210071319721383/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree036.table
  base := (-3350868420057386381466770791098882448171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-8185682607886493711959316147297355000000000000)
      constant := (75171913207647057148052499263289926020940195686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree036.table
  base := (-6702584988106304332893508877395195363771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-26800076915760426771520585965000000000000)
      constant := (246395455164114913961239106142604804636229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59093684028527888553/20000000000000000000)
  centralHi := (147734210071319721383/50000000000000000000)
  directionLo := (149829835452878792427/50000000000000000000)
  directionHi := (59931934181151516971/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree037.table
  base := (-3420473414842333179094238619131939040331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-8412691898638103991187034095623135000000000000)
      constant := (79471813444436977545661237047331591290910222246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree037.table
  base := (-855208812732282146366789182585654757809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-578409528239433349374246097305000000000000)
      constant := (5470272395471298979476163438180610000688088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149829835452878792427/50000000000000000000)
  centralHi := (59931934181151516971/20000000000000000000)
  directionLo := (151896551502253151023/50000000000000000000)
  directionHi := (303793103004506302047/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree038.table
  base := (-1736953601290659171411976451255303195697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-23932690275317768062090725883515000000000000)
      constant := (232411033924735119359191252039332032772978564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree038.table
  base := (-6948431871217055800321356150810676116149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-594017441247897736546559889345000000000000)
      constant := (5775094613009065206952579966762975801560871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151896551502253151023/50000000000000000000)
  centralHi := (303793103004506302047/100000000000000000000)
  directionLo := (9620970163836079389/3125000000000000000)
  directionHi := (307871045242754540449/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree039.table
  base := (-7022864397574750761583906257991636965291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-8866710480141324549642469992274695000000000000)
      constant := (88457462138815911343708449307783348640033866803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree039.table
  base := (-351169562610070412681193392032725206539/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-203208451418787374572957893795000000000000)
      constant := (2029586748594439668977105655330418471084540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9620970163836079389/3125000000000000000)
  centralHi := (307871045242754540449/100000000000000000000)
  directionLo := (31189567416786313989/10000000000000000000)
  directionHi := (311895674167863139891/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree040.table
  base := (-1766632410361742276351759256629346771761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-9093719770892934828870187940600475000000000000)
      constant := (93142917773882077940643850792820358102555817252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree040.table
  base := (-1766744798180639082358798821676503225423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-625233267264826510891187473425000000000000)
      constant := (6411260252287924301641914153979173729064468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31189567416786313989/10000000000000000000)
  centralHi := (311895674167863139891/100000000000000000000)
  directionLo := (12634761106115808949/4000000000000000000)
  directionHi := (157934513826447611863/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree041.table
  base := (-176979185687664443805499148797163983817/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1331532723092077872585415126989465000000000000)
      constant := (13993805843473438258625572714783250700915584920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree041.table
  base := (-7079551030068216478780576857001806683807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-640841180273290898063501265465000000000000)
      constant := (6742587170439839045612841524997962059640053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12634761106115808949/4000000000000000000)
  centralHi := (157934513826447611863/50000000000000000000)
  directionLo := (159896508479817285781/50000000000000000000)
  directionHi := (319793016959634571563/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree042.table
  base := (-7061072951692645374048416576284345873607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1363962621770879341046517691036005000000000000)
      constant := (14699791609847882820324947789921028487894972633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree042.table
  base := (-8826750365223383710224521553264710961/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-31259480632464537392181669405000000000000)
      constant := (337273087435824597868913684787388231231200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159896508479817285781/50000000000000000000)
  centralHi := (319793016959634571563/100000000000000000000)
  directionLo := (161834718742537413773/50000000000000000000)
  directionHi := (323669437485074827547/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree043.table
  base := (-219140322503416657521160341035189056739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-9774747643147765666553341785577815000000000000)
      constant := (107968544228154262718505856159497734626018757984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree043.table
  base := (-3506384830721567676658123928518316679963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-96008143755745667486875549935000000000000)
      constant := (1061671164727883653125084165843890099920222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161834718742537413773/50000000000000000000)
  centralHi := (323669437485074827547/100000000000000000000)
  directionLo := (327499978362845696071/100000000000000000000)
  directionHi := (40937497295355712009/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree044.table
  base := (-6933621563257283898924162998221519857097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-82659148214044429303975700280195000000000000)
      constant := (935261057914968814760326925332784219321115881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree044.table
  base := (-3466929976761354131138717303078280118331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-687664919298684059580442641585000000000000)
      constant := (7789472904139560756308220582090712235030098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327499978362845696071/100000000000000000000)
  centralHi := (40937497295355712009/12500000000000000000)
  directionLo := (331286231065258787161/100000000000000000000)
  directionHi := (165643115532629393581/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree045.table
  base := (-6824634027129986049864355185284041386173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-10228766224650986225008777682229375000000000000)
      constant := (118492621438723680468554388624786817017474040309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree045.table
  base := (-3412418739020618998402856924561733409311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-234424277435716148917585477875000000000000)
      constant := (2718685198927780683402829460181135732269646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331286231065258787161/100000000000000000000)
  centralHi := (165643115532629393581/50000000000000000000)
  directionLo := (335029697130244968183/100000000000000000000)
  directionHi := (41878712141280621023/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree046.table
  base := (-104463538117625487644621684135767200813/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-10455775515402596504236495630555155000000000000)
      constant := (123946602102808220839018147195794932699776731456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree046.table
  base := (-668584007882944229521301065162494214549/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-718880745315612833925070225665000000000000)
      constant := (8531443336306084381071842129885876214944710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335029697130244968183/100000000000000000000)
  centralHi := (41878712141280621023/12500000000000000000)
  directionLo := (10585368597487345023/3125000000000000000)
  directionHi := (338731795119595040737/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree047.table
  base := (-6516833893992422780559092219098978864399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-10682784806154206783464213578880935000000000000)
      constant := (129528494808158095709724886790078060029569310967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree047.table
  base := (-1629245523883677528253429825657412759657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-734488658324077221097384017705000000000000)
      constant := (8915633721575192580832479550049777328188812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10585368597487345023/3125000000000000000)
  centralHi := (338731795119595040737/100000000000000000000)
  directionLo := (68478773379990663453/20000000000000000000)
  directionHi := (171196933449976658633/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree048.table
  base := (-6318231948497961606329771543764440211673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1558542013843688151813133075315245000000000000)
      constant := (19319752905185432021635562700705905487113911687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree048.table
  base := (-315917922160971766870108441400807840403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-250032190444180536089899269915000000000000)
      constant := (3102874919791452125953106577163886902343580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68478773379990663453/20000000000000000000)
  centralHi := (171196933449976658633/50000000000000000000)
  directionLo := (69203436665085523781/20000000000000000000)
  directionHi := (173008591662713809453/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree049.table
  base := (-6089939999401323274889182086522594492441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1590971912522489620274235639361785000000000000)
      constant := (20153700630063173505653721054298714049975684679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree049.table
  base := (-6090047969990025575009793206039625013437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-109386354905857999348858800255000000000000)
      constant := (1387202113413334458916157508666881124959689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69203436665085523781/20000000000000000000)
  centralHi := (173008591662713809453/50000000000000000000)
  directionLo := (349602949390050515663/100000000000000000000)
  directionHi := (21850184336878157229/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree050.table
  base := (-5832024061437700650326827723316939116621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-11363812678409037621147367423858275000000000000)
      constant := (147041376845463131157632156883891424477128146693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree050.table
  base := (-5832116223056938414153167246012227784909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-111616056764210054659189341975000000000000)
      constant := (1445857492662961067877025709511963316645273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349602949390050515663/100000000000000000000)
  centralHi := (21850184336878157229/6250000000000000000)
  directionLo := (353152308909317283271/100000000000000000000)
  directionHi := (44144038613664660409/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree051.table
  base := (-2772269530232387682265993202215415552613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-11590821969160647900375085372184055000000000000)
      constant := (153134670846846048266079378565318325565448361658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree051.table
  base := (-1386154432395899687785586299430343869909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-265640103452644923262213061955000000000000)
      constant := (3513462192848694414405013603330950371642548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353152308909317283271/100000000000000000000)
  centralHi := (44144038613664660409/12500000000000000000)
  directionLo := (44583293597795249523/12500000000000000000)
  directionHi := (71333269756472399237/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree052.table
  base := (-209101229043436016490365602299472311151/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-11817831259912258179602803320509835000000000000)
      constant := (159355772431987337429770618748808341245907304575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree052.table
  base := (-5227597879161692246505444148774826688193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-812528223366399156958952977905000000000000)
      constant := (10968566230427983117769594632055728639547947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44583293597795249523/12500000000000000000)
  centralHi := (71333269756472399237/20000000000000000000)
  directionLo := (22509131429986948829/6250000000000000000)
  directionHi := (72029220575958236253/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree053.table
  base := (-488103715537878168671372892108089884083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-12044840550663868458830521268835615000000000000)
      constant := (165704669952057839750858129588926679304135933390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree053.table
  base := (-4881094478885590001155332701013291397/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-828136136374863544131266769945000000000000)
      constant := (11405540610337445305683671192133720880663000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22509131429986948829/6250000000000000000)
  centralHi := (72029220575958236253/20000000000000000000)
  directionLo := (363592555596591898889/100000000000000000000)
  directionHi := (36359255559659189889/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree054.table
  base := (-4505090106013466289613983236756626229981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-12271849841415478738058239217161395000000000000)
      constant := (172181353696610057937190832979407301667537399573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree054.table
  base := (-1126284759772963140948876601356959771579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-281248016461109310434526853995000000000000)
      constant := (3950436352185800678478165694552005126395788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363592555596591898889/100000000000000000000)
  centralHi := (36359255559659189889/10000000000000000000)
  directionLo := (367006645104717972003/100000000000000000000)
  directionHi := (91751661276179493001/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree055.table
  base := (-512464508312667566927332964354369942239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (256111663457074716782058133020000000000000)
      linear := (-14756622352027259760668190278025000000000000)
      constant := (211081246241241240766889748564507079606813768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree055.table
  base := (-512469729664832477039992284222211244197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-859351962391792318475894354025000000000000)
      constant := (12305871017259551529502298873375668510974904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367006645104717972003/100000000000000000000)
  centralHi := (91751661276179493001/25000000000000000000)
  directionLo := (370389266335810608019/100000000000000000000)
  directionHi := (18519463316790530401/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree056.table
  base := (-458117142840142096220452949667720002127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-1817981203274099899501953587687565000000000000)
      constant := (26502578400281919482117777687837534580696724104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree056.table
  base := (-1832486399735575029570951108913091434567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-124994267914322386521172592295000000000000)
      constant := (1824175147428555126225485401306521451392598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370389266335810608019/100000000000000000000)
  centralHi := (18519463316790530401/5000000000000000000)
  directionLo := (1868706368604626997/500000000000000000)
  directionHi := (373741273720925399401/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree057.table
  base := (-64015435857041740323568182878161973761/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-35880547683297256442496933690135000000000000)
      constant := (532903179389568656606256937812782340411221650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree057.table
  base := (-3200802230185952299035809868926900152477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-42407989924224813943834378005000000000000)
      constant := (630541605541954089929549106986073099847523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1868706368604626997/500000000000000000)
  centralHi := (373741273720925399401/100000000000000000000)
  directionLo := (188531741855515751589/50000000000000000000)
  directionHi := (377063483711031503179/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree058.table
  base := (-1353617718556048563201065584488923195899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-13179887004421919854969111010464515000000000000)
      constant := (199365807724320108491089836544392485842319100934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree058.table
  base := (-676815354668966207946356851456980525423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-906175701417185479992835730145000000000000)
      constant := (13722313749329532780117240096307613635864468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188531741855515751589/50000000000000000000)
  centralHi := (377063483711031503179/100000000000000000000)
  directionLo := (380356677099349679493/100000000000000000000)
  directionHi := (190178338549674839747/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree059.table
  base := (-1092170482005251776178087771073235603007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-13406896295173530134196828958790295000000000000)
      constant := (206481324755150072464623043403608327438750717262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree059.table
  base := (-109218157083221908529808020021937952291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-921783614425649867165149522185000000000000)
      constant := (14212045862534181997591210840935786060037780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380356677099349679493/100000000000000000000)
  centralHi := (190178338549674839747/50000000000000000000)
  directionLo := (191810800582122195901/50000000000000000000)
  directionHi := (383621601164244391803/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree060.table
  base := (-408024787746643814393507426592224300291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-13633905585925140413424546907116075000000000000)
      constant := (213724595556738904002285631273091951409491687212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree060.table
  base := (-816059040598245467518979307825423039691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-312463842478038084779154438075000000000000)
      constant := (4903523277224014116643824845190444077444326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191810800582122195901/50000000000000000000)
  centralHi := (383621601164244391803/100000000000000000000)
  directionLo := (48357371456166430717/12500000000000000000)
  directionHi := (386858971649331445737/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree061.table
  base := (-1050519014159168149444774371784028919597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-13860914876676750692652264855441855000000000000)
      constant := (221095617372254988889842963111346315329341584101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree061.table
  base := (-210107034395477216013647008137031454841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-952999440442578641509777106265000000000000)
      constant := (15217885469114301215083925507440611697241695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48357371456166430717/12500000000000000000)
  centralHi := (386858971649331445737/100000000000000000000)
  directionLo := (390069474595664648351/100000000000000000000)
  directionHi := (12189671081114520261/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree062.table
  base := (-10990202483306015431899720101496601979/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2012560595346908710268568971966805000000000000)
      constant := (32656341127777212597495946904149416077158212040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree062.table
  base := (-439621890323925168315321535321679531249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-968607353451043028682090898305000000000000)
      constant := (15733992617858305760233368787488244729843771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390069474595664648351/100000000000000000000)
  centralHi := (12189671081114520261/3125000000000000000)
  directionLo := (196626884019643601779/50000000000000000000)
  directionHi := (393253768039287203559/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree063.table
  base := (50156818929579062732722978131264060731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2044990494025710178729671536013345000000000000)
      constant := (33745843598789717284266670303539449481747163244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree063.table
  base := (20061550530037670075673649776212164957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-46867393640928924564495461445000000000000)
      constant := (774232911736967722299574258202762121649570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196626884019643601779/50000000000000000000)
  centralHi := (393253768039287203559/100000000000000000000)
  directionLo := (79282496717209188267/20000000000000000000)
  directionHi := (49551560448255742667/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree064.table
  base := (870181819393118169472116241410417792167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-14541942748931581530335418700419195000000000000)
      constant := (243975167645521118377141375502457579217057527089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree064.table
  base := (870171773927097112138168353025253199129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-142831882781138829003816926055000000000000)
      constant := (2398940134986859081220256032419075759597387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79282496717209188267/20000000000000000000)
  centralHi := (49551560448255742667/12500000000000000000)
  directionLo := (49943278484292930809/12500000000000000000)
  directionHi := (399546227874343446473/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree065.table
  base := (62762043920117579221403211355358154847/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-14768952039683191809563136648744975000000000000)
      constant := (251857173900743926882583292005792657423327566225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree065.table
  base := (196130315636244150589995801554440015351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1015431092476436190199032274425000000000000)
      constant := (17335061920953588020902278041536145922578968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/12500000000000000000)
  centralHi := (399546227874343446473/100000000000000000000)
  directionLo := (201327791967711463073/50000000000000000000)
  directionHi := (402655583935422926147/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree066.table
  base := (2297231395418025581578838539641660386407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-123933564714337207345378963612155000000000000)
      constant := (2147660519181211568848242184727189475796450489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree066.table
  base := (287153009945009969128952702513399077909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-343679668494966859123782022155000000000000)
      constant := (5962111332449746451879212058630750348362904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201327791967711463073/50000000000000000000)
  centralHi := (402655583935422926147/100000000000000000000)
  directionLo := (202870556229912313033/50000000000000000000)
  directionHi := (405741112459824626067/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree067.table
  base := (3054719595936688108300488449994367894749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-15222970621186412368018572545396535000000000000)
      constant := (268004413453390379075215606934386675388073717483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree067.table
  base := (610942670628174048978043401775831796207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1046646918493364964543659858505000000000000)
      constant := (18446397109326838835992025373691462338601735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202870556229912313033/50000000000000000000)
  centralHi := (405741112459824626067/100000000000000000000)
  directionLo := (408803352977804832987/100000000000000000000)
  directionHi := (102200838244451208247/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree068.table
  base := (3841513086479802188086641675332158636511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-15449979911938022647246290493722315000000000000)
      constant := (276269644999141899841393821840545398149810058937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree068.table
  base := (3841507759652595493483899604060358770387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1062254831501829351715973650545000000000000)
      constant := (19015251202576612149042396722465267534178127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408803352977804832987/100000000000000000000)
  centralHi := (102200838244451208247/25000000000000000000)
  directionLo := (41184282496075530003/10000000000000000000)
  directionHi := (411842824960755300031/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree069.table
  base := (4657609674881003489570832124792237879113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2239569886098518989496286920292585000000000000)
      constant := (40666088112555575629523288404751607242797534953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree069.table
  base := (4657605129896690539786544414337459285903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-359287581503431246296095814195000000000000)
      constant := (6530965410515129810216400532465362215001321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41184282496075530003/10000000000000000000)
  centralHi := (411842824960755300031/100000000000000000000)
  directionLo := (51857503606248814911/12500000000000000000)
  directionHi := (414860028849990519289/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree070.table
  base := (1375751880397643048065053786124596835039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2271999784777320457957389484339125000000000000)
      constant := (41883332608165452655810080325893209057405354236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree070.table
  base := (5503003643934809287957277019323375052909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-156210093931251160865800176375000000000000)
      constant := (2882761736859209344685683090807970125158727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51857503606248814911/12500000000000000000)
  centralHi := (414860028849990519289/100000000000000000000)
  directionLo := (208927723509336239533/50000000000000000000)
  directionHi := (417855447018672479067/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree071.table
  base := (6377705082564520340440424477671105212277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-16131007784192853484929444338699655000000000000)
      constant := (301831778934831619328161537557282338327442301459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree071.table
  base := (1275540354893747782603744372771902563213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-158439795789603216176130718095000000000000)
      constant := (2967794135701511089452801707226578538448195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208927723509336239533/50000000000000000000)
  centralHi := (417855447018672479067/100000000000000000000)
  directionLo := (84165908934421718241/20000000000000000000)
  directionHi := (210414772336054295603/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree072.table
  base := (7281701061485929244342211932376922453863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-16358017074944463764157162287025435000000000000)
      constant := (310607968424538446342121270949447954447950327921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree072.table
  base := (3640849119740318682654491784911201507257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-374895494511895633468409606235000000000000)
      constant := (7126192193437117129238597579748756821101598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84165908934421718241/20000000000000000000)
  centralHi := (210414772336054295603/50000000000000000000)
  directionLo := (211891385345590369963/50000000000000000000)
  directionHi := (423782770691180739927/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree073.table
  base := (8214994369776783132709070613181110868423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-16585026365696074043384880235351215000000000000)
      constant := (319511896393427415484219974113852921226905095441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree073.table
  base := (8214991962602419380332391014666658261541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1140294396544151287577542610745000000000000)
      constant := (21991385026613056906883914908062999823492361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211891385345590369963/50000000000000000000)
  centralHi := (423782770691180739927/100000000000000000000)
  directionLo := (213357779211617636027/50000000000000000000)
  directionHi := (85343111684647054411/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree074.table
  base := (9177584093116638856281149885553879937043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-16812035656447684322612598183676995000000000000)
      constant := (328543562561929507814037910301528968206709826981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree074.table
  base := (2294395509984911496641651683705911676719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1155902309552615674749856402785000000000000)
      constant := (22612984269833910965272009370301296580844396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213357779211617636027/50000000000000000000)
  centralHi := (85343111684647054411/20000000000000000000)
  directionLo := (21481416321218973103/5000000000000000000)
  directionHi := (429628326424379462061/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree075.table
  base := (10169469463398686047280803030888385808143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-17039044947199294601840316132002775000000000000)
      constant := (337702966695183008245850811808267836563398460681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree075.table
  base := (10169467712288155681047495192651940749399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-390503407520360020640723398275000000000000)
      constant := (7747791431343542057105943093223563585245793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21481416321218973103/5000000000000000000)
  centralHi := (429628326424379462061/100000000000000000000)
  directionLo := (432521479156784523631/100000000000000000000)
  directionHi := (27032592447299032727/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree076.table
  base := (11190649835231679897329628541350467029871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85843521546554129447725856220000000000000)
      linear := (-6832629298753820688986163070965000000000000)
      constant := (137313062364799593204723086640373406510614391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree076.table
  base := (11190648341858469593664053545528942984503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1187118135569544449094483986865000000000000)
      constant := (23882555085809623468749043576476107802674563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432521479156784523631/100000000000000000000)
  centralHi := (27032592447299032727/6250000000000000000)
  directionLo := (435395407644284215989/100000000000000000000)
  directionHi := (43539540764428421599/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree077.table
  base := (2448224933248824518736632474072086766701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (256111663457074716782058133020000000000000)
      linear := (-20652967566354799480868656468305000000000000)
      constant := (420785109915096686410604200896417616613895305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree077.table
  base := (12241123392769931494414107395603943111509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-171818006939715548038113968415000000000000)
      constant := (3504360947702487010962229514051811829334527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435395407644284215989/100000000000000000000)
  centralHi := (43539540764428421599/10000000000000000000)
  directionLo := (109562622522319416997/25000000000000000000)
  directionHi := (438250490089277667989/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree078.table
  base := (1332089350057008431316999972477547169241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-17720072819454125439523469976980115000000000000)
      constant := (365947605062509214565948715536009306652973128470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree078.table
  base := (2664178482939747228897805931952002343411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-58015902932689201116148170045000000000000)
      constant := (1199394710899865861202977960789760011717055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109562622522319416997/25000000000000000000)
  centralHi := (438250490089277667989/100000000000000000000)
  directionLo := (6891985819588935137/1562500000000000000)
  directionHi := (441087092453691848769/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree079.table
  base := (14429955954998444038763374431328913864483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-17947082110205735718751187925305895000000000000)
      constant := (375617959371942220716822888857953125505601373461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree079.table
  base := (577198201166627536553532512945347661573/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1233941874594937610611425362985000000000000)
      constant := (25852841962800882396598774653341307522325825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6891985819588935137/1562500000000000000)
  centralHi := (441087092453691848769/100000000000000000000)
  directionLo := (110976392251632547909/25000000000000000000)
  directionHi := (443905569006530191637/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree080.table
  base := (15568311707352607296610278101720266660457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-18174091400957345997978905873631675000000000000)
      constant := (385416050927874941079917665309231700775967955519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree080.table
  base := (7784155459017107794370897650651694458359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1249549787603401997783739155025000000000000)
      constant := (26527185728947638983756195635327371167251078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110976392251632547909/25000000000000000000)
  centralHi := (443905569006530191637/100000000000000000000)
  directionLo := (111676565710081656061/25000000000000000000)
  directionHi := (89341252568065324849/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree081.table
  base := (16735960486738826110876596004276648656513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-18401100691708956277206623821957455000000000000)
      constant := (395341879647477007017906175130685610529756010471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree081.table
  base := (8367979906929857419333521581222493586567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-421719233537288794985350982355000000000000)
      constant := (9070106740573705395764539670002114910211938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/25000000000000000000)
  centralHi := (89341252568065324849/20000000000000000000)
  directionLo := (224744753179318188641/50000000000000000000)
  directionHi := (449489506358636377283/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree082.table
  base := (358658041307210170870471238311381627587/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-18628109982460566556434341770283235000000000000)
      constant := (405395445461095738003670118890475646306119711450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree082.table
  base := (8966450745895073143393454905171041185093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1280765613620330772128366739105000000000000)
      constant := (27902245436399421169797674698847183729773906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/50000000000000000000)
  centralHi := (449489506358636377283/100000000000000000000)
  directionLo := (56531952717065551117/12500000000000000000)
  directionHi := (452255621736524408937/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree083.table
  base := (19159136251645350475510336465983417353421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2693588467601739547951722816944145000000000000)
      constant := (59368106901450663617663248036724714153414782701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree083.table
  base := (9579567881383428864642817407783272576171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1296373526628795159300680531145000000000000)
      constant := (28602961369012322234988231732831897448199182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56531952717065551117/12500000000000000000)
  centralHi := (452255621736524408937/100000000000000000000)
  directionLo := (455004921355857300161/100000000000000000000)
  directionHi := (227502460677928650081/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree084.table
  base := (20414662884473399384268120545839653242381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2726018366280541016412825380990685000000000000)
      constant := (60840826877912652064979390461872591893280444461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree084.table
  base := (10207331233907794440566768787063044451887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-62475306649393311736809253485000000000000)
      constant := (1395831810296255234137126991394126088903774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455004921355857300161/100000000000000000000)
  centralHi := (227502460677928650081/50000000000000000000)
  directionLo := (228868854108531729137/50000000000000000000)
  directionHi := (18309508328682538331/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree085.table
  base := (2169948182832863606100869692091267849213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-19309137854715397394117495615260575000000000000)
      constant := (436322564925361168751895562999523769464503113710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree085.table
  base := (867979258930072412274214096374217545353/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-189655621806531990520758302175000000000000)
      constant := (4290109339317022728189571339853066315901475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228868854108531729137/50000000000000000000)
  centralHi := (18309508328682538331/4000000000000000000)
  directionLo := (460454276328898004293/100000000000000000000)
  directionHi := (230227138164449002147/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree086.table
  base := (4602718593845094067172535698107088133341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-19536147145467007673345213563586355000000000000)
      constant := (446887078615219426265291772670710215086336387735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree086.table
  base := (11506796333326566454537586666477568534783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1343197265654188320817621907265000000000000)
      constant := (30757853443644849605285335386162057878460886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460454276328898004293/100000000000000000000)
  centralHi := (230227138164449002147/50000000000000000000)
  directionLo := (231577455538815780353/50000000000000000000)
  directionHi := (463154911077631560707/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree087.table
  base := (24356996211285633561970368297448382362849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-19763156436218617952572931511912135000000000000)
      constant := (457579329185646926425700013287137097029941250183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree087.table
  base := (12178497976737707390682046778804599138471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-452935059554217569329978566435000000000000)
      constant := (10497910739837668153573222599438264387938594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231577455538815780353/50000000000000000000)
  centralHi := (463154911077631560707/100000000000000000000)
  directionLo := (232919944788487593449/50000000000000000000)
  directionHi := (465839889576975186899/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree088.table
  base := (25729691473861097373150630185791738775563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-165207981214629985386782226944115000000000000)
      constant := (3871068732330447632592381631320955723885847701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree088.table
  base := (25729691254209171939317454801398533516979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1374413091671117095162249491345000000000000)
      constant := (32238401701153924499957498791509369203856559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232919944788487593449/50000000000000000000)
  centralHi := (465839889576975186899/100000000000000000000)
  directionLo := (46850948099995593639/10000000000000000000)
  directionHi := (468509480999955936391/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree089.table
  base := (27131678689115506799115001314357686401071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-20217175017721838511028367408563695000000000000)
      constant := (479347040873489018869026072561238259197796276457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree089.table
  base := (13565839250994807710790607117183586852617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1390021004679581482334563283385000000000000)
      constant := (32991861887163449154810393466316710647809914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46850948099995593639/10000000000000000000)
  centralHi := (468509480999955936391/100000000000000000000)
  directionLo := (235581973446934023763/50000000000000000000)
  directionHi := (471163946893868047527/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree090.table
  base := (28562957799990728657789336529991528844711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2920597758353349827179440765269925000000000000)
      constant := (70060357421816428313294347665757184971465821191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree090.table
  base := (28562957640587628360337073043137242373409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-468542972562681956502292358475000000000000)
      constant := (11251370925453588990351389182551960696613863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235581973446934023763/50000000000000000000)
  centralHi := (471163946893868047527/100000000000000000000)
  directionLo := (473803541479342835587/100000000000000000000)
  directionHi := (118450885369835708897/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree091.table
  base := (1200941150339877402008958248496315972067/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-2953027657032151295640543329316465000000000000)
      constant := (71660814262141199401229016285509421949396465675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree091.table
  base := (6004705724544142319128994479404004972241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-203033832956644322382741552495000000000000)
      constant := (4932164909678992209475725685726060074583615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473803541479342835587/100000000000000000000)
  centralHi := (118450885369835708897/25000000000000000000)
  directionLo := (14888390997953288167/3125000000000000000)
  directionHi := (95285702386901044269/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree092.table
  base := (31513391524274543290231746482785638270131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-20898202889976669348711521253541035000000000000)
      constant := (512956634507968583196446738326649726256943145477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree092.table
  base := (31513391408632739167455096087029373680837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-205263534814996377693072094215000000000000)
      constant := (5043569522929300856496726297601088121042511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14888390997953288167/3125000000000000000)
  centralHi := (95285702386901044269/20000000000000000000)
  directionLo := (479039098665115874187/100000000000000000000)
  directionHi := (119759774666278968547/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree093.table
  base := (16516273031692315845974528227457141023441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-21125212180728279627939239201866815000000000000)
      constant := (524415305961278158089469835704027697778628968494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree093.table
  base := (3303254596489958731988480619448096850131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-484150885571146343674606150515000000000000)
      constant := (12031203217971780653207215000246366779509170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479039098665115874187/100000000000000000000)
  centralHi := (119759774666278968547/25000000000000000000)
  directionLo := (96327107112306919627/20000000000000000000)
  directionHi := (60204441945191824767/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree094.table
  base := (34580992347291407289320432853899478696097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-21352221471479889907166957150192595000000000000)
      constant := (536001714186191816679820528349195246902469491399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree094.table
  base := (17290496131712296285827346236830610251637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1468060569721903418196132243585000000000000)
      constant := (36891023347393623425656894937516885630568754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96327107112306919627/20000000000000000000)
  centralHi := (60204441945191824767/12500000000000000000)
  directionLo := (484218050243282334923/100000000000000000000)
  directionHi := (121054512560820583731/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree095.table
  base := (7231746070401227094512619706256263807311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-59776262499256233203309349303375000000000000)
      constant := (1517218446469181705130386054963432777223962085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree095.table
  base := (18079365140296786513190555352225192708821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1483668482730367805368446035625000000000000)
      constant := (37697227740444052573758777364918458093770482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484218050243282334923/100000000000000000000)
  centralHi := (121054512560820583731/25000000000000000000)
  directionLo := (121696716072981385133/25000000000000000000)
  directionHi := (486786864291925540533/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree096.table
  base := (1510630402294673414677639277333141419333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-21806240052983110465622393046844155000000000000)
      constant := (559557740922661626300090923791069906309129835275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree096.table
  base := (18882879998281996852669358862251277797681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-499758798579610730846919942555000000000000)
      constant := (12837407610883312056458020025511517889167534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121696716072981385133/25000000000000000000)
  centralHi := (486786864291925540533/100000000000000000000)
  directionLo := (122335548368239324001/25000000000000000000)
  directionHi := (97868438694591459201/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree097.table
  base := (4925260180804018899772664365326976434639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3147607049104960106407158713595705000000000000)
      constant := (81646765631838971627550448671704448761131729272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree097.table
  base := (3940208139466692275531450993163084198501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1514884308747296579713073619705000000000000)
      constant := (39336008623661226643585269996719247681685210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/25000000000000000000)
  centralHi := (97868438694591459201/20000000000000000000)
  directionLo := (491884247947303967389/100000000000000000000)
  directionHi := (49188424794730396739/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree098.table
  base := (20533847252485628255228540163607019123523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3180036947783761574868261277642245000000000000)
      constant := (83374959238808114816776736716396241404669216326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree098.table
  base := (20533847230451918767202543062911309293947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-218641745965108709555055344535000000000000)
      constant := (5738369301883422145844633671467467855763682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491884247947303967389/100000000000000000000)
  centralHi := (49188424794730396739/10000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree099.table
  base := (42762599221034541676227047488303820412641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-185845189464776374407483858610095000000000000)
      constant := (4924378567482312702370732010369771254182743807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree099.table
  base := (8552519836704640740158247816633742534073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-73623815941153588288461962085000000000000)
      constant := (1952854871474825670484635896928168712670365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (248464673298944090371/50000000000000000000)
  directionHi := (496929346597888180743/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree100.table
  base := (44486795584592264989693771003881026720447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-22714277215989551582533264840147275000000000000)
      constant := (608202635400915137168960821933602439897230917849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree100.table
  base := (44486795552664155119058011031346374099547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1561708047772689741230014995825000000000000)
      constant := (41860110186816300632536310289158273856090487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248464673298944090371/50000000000000000000)
  centralHi := (496929346597888180743/100000000000000000000)
  directionLo := (499432784842929308091/100000000000000000000)
  directionHi := (124858196210732327023/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree101.table
  base := (23120141793615194273310048232771477212821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-22941286506741161861760982788473055000000000000)
      constant := (620683200875749969135879021059359975045865277414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree101.table
  base := (11560070890014155452512319087292191058387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1577315960781154128402328787865000000000000)
      constant := (42719058770545168208427026423227544048904508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499432784842929308091/100000000000000000000)
  centralHi := (124858196210732327023/25000000000000000000)
  directionLo := (62740467109768376649/12500000000000000000)
  directionHi := (501923736878147013193/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree102.table
  base := (24011531610947267353964712667842031923797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-23168295797492772140988700736798835000000000000)
      constant := (633291503087707337000045636326966894150487274598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree102.table
  base := (48023063198768949395172856148614459495507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-530974624596539505191547526635000000000000)
      constant := (14528932684004125688633022160350301216468549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62740467109768376649/12500000000000000000)
  centralHi := (501923736878147013193/100000000000000000000)
  directionLo := (504402387690108970203/100000000000000000000)
  directionHi := (126100596922527242551/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree103.table
  base := (49835134482674439688791373865517718997523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-23395305088244382420216418685124615000000000000)
      constant := (646027542034980077134764435788707953884715615141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree103.table
  base := (49835134462995478534711489142292957894349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1608531786798082902746956371945000000000000)
      constant := (44463328031096008358818367975593152115781329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504402387690108970203/100000000000000000000)
  centralHi := (126100596922527242551/25000000000000000000)
  directionLo := (253434458871146126541/50000000000000000000)
  directionHi := (506868917742292253083/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree104.table
  base := (51676497364622491678894860512444771135661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3374616339856570385634876661921485000000000000)
      constant := (94127331102293624731376004424935320047976808141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree104.table
  base := (51676497347877750312967264417872905489663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1624139699806547289919270163985000000000000)
      constant := (45348648707694034449955274777695331015282923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253434458871146126541/50000000000000000000)
  centralHi := (506868917742292253083/100000000000000000000)
  directionLo := (254661751564208336051/50000000000000000000)
  directionHi := (509323503128416672103/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree105.table
  base := (10709430372720191749145878508058695174649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3407046238535371854095979225968025000000000000)
      constant := (95983261447095434724977212293146246819619214845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree105.table
  base := (53547151849354009910887816381174084252823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-78083219657857698909123045525000000000000)
      constant := (2202036194367674213719508914756174084252823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254661751564208336051/50000000000000000000)
  centralHi := (509323503128416672103/100000000000000000000)
  directionLo := (127941578929789744281/25000000000000000000)
  directionHi := (4094130525753271817/800000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree106.table
  base := (55447097976153367514336659470627752756707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-24076332960499213257899572530101955000000000000)
      constant := (685002079274761211505948923301077451077160029269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree106.table
  base := (27723548982016263429274933122201576349483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-236479360831925152037699678295000000000000)
      constant := (6735094593300879161916173773943209458096898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127941578929789744281/25000000000000000000)
  centralHi := (4094130525753271817/800000000000000000)
  directionLo := (514197523302593846663/100000000000000000000)
  directionHi := (64274690412824230833/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree107.table
  base := (448252622651532915518938539520269931937/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-24303342251250823537127290478427735000000000000)
      constant := (698249065150453197801297831237864427663658326912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree107.table
  base := (57376335689084961365083912929693463752833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1670963438831940451436211540105000000000000)
      constant := (48057354921789626250257602878228562738809493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514197523302593846663/100000000000000000000)
  centralHi := (64274690412824230833/12500000000000000000)
  directionLo := (516617289718686417811/100000000000000000000)
  directionHi := (129154322429671604453/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree108.table
  base := (59334865030927786618882646099234692495793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-24530351542002433816355008426753515000000000000)
      constant := (711623787756009638561326149133625904220361138231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree108.table
  base := (59334865022156604234871393054900972693597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-562190450613468279536175110715000000000000)
      constant := (16325946129240708648511618920244306808855179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516617289718686417811/100000000000000000000)
  centralHi := (129154322429671604453/25000000000000000000)
  directionLo := (259512887494070714179/50000000000000000000)
  directionHi := (519025774988141428359/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree109.table
  base := (61322685968751413190434828231859037604661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-24757360832754044095582726375079295000000000000)
      constant := (725126247090820016577109759285285044851264379987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree109.table
  base := (30661342980645410391369104215910263333657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1702179264848869225780839124185000000000000)
      constant := (49907112550862563890856322003163231060013594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259512887494070714179/50000000000000000000)
  centralHi := (519025774988141428359/100000000000000000000)
  directionLo := (260711567717947861253/50000000000000000000)
  directionHi := (521423135435895722507/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree110.table
  base := (63339798511210826378672540051132950811917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-206482397714922763428185490276075000000000000)
      constant := (6105425150036180993412326381250337966701714259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree110.table
  base := (63339798504865452139279193431154178952313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1717787177857333612953152916225000000000000)
      constant := (50845177411176874749964490127304237757998573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260711567717947861253/50000000000000000000)
  centralHi := (521423135435895722507/100000000000000000000)
  directionLo := (523809523809523809523/100000000000000000000)
  directionHi := (130952380952380952381/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree111.table
  base := (65386202656935759224238127262004836934209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3601625630608180664862594610247265000000000000)
      constant := (107502053706609186717329919398686915782123183329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree111.table
  base := (4086637665721205196067114700275643878361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-577798363621932666708488902755000000000000)
      constant := (17264010989545631001447843454445872114376432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523809523809523809523/100000000000000000000)
  centralHi := (130952380952380952381/25000000000000000000)
  directionLo := (263092544696405131663/50000000000000000000)
  directionHi := (526185089392810263327/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree112.table
  base := (67461898404796139989522775345864172432087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3634055529286982133323697174293805000000000000)
      constant := (109485720780876242626767165124989372916005992247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree112.table
  base := (13492379680041397058788191682551712783817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-249857571982037483899682928615000000000000)
      constant := (7535382746174200965123948289878275691757255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263092544696405131663/50000000000000000000)
  centralHi := (526185089392810263327/100000000000000000000)
  directionLo := (26427498905736396089/5000000000000000000)
  directionHi := (528549978114727921781/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree113.table
  base := (69566885753863533412020612500127551979139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-25665397995760485212493598168382415000000000000)
      constant := (780413451713702189436163019480181973686005394613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree113.table
  base := (69566885749961195252020416674339213832347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-252087273840389539210013470335000000000000)
      constant := (7673159453557908767717392864388017641497041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/5000000000000000000)
  centralHi := (528549978114727921781/100000000000000000000)
  directionLo := (530904332654047006193/100000000000000000000)
  directionHi := (265452166327023503097/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree114.table
  base := (71701164703378683642286514245042567074183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-71724119907235721583715557109995000000000000)
      constant := (2200982256755505885829281826121266054311833001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree114.table
  base := (17925291175015150236366230062040653870151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-593406276630397053880802694795000000000000)
      constant := (18228447941226396435141024447827138308364228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530904332654047006193/100000000000000000000)
  centralHi := (265452166327023503097/50000000000000000000)
  directionLo := (26662414626989367983/5000000000000000000)
  directionHi := (533248292539787359661/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree115.table
  base := (2954589410108967826402224740092998576881/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-26119416577263705770949034065033975000000000000)
      constant := (808823474391051225408831989040620084896429318175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree115.table
  base := (73864735249903086102578570985307571077207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1795826742899655548814721876425000000000000)
      constant := (55667362169528246108365994046316458992621347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26662414626989367983/5000000000000000000)
  centralHi := (533248292539787359661/100000000000000000000)
  directionLo := (535581994247713929477/100000000000000000000)
  directionHi := (267790997123856964739/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree116.table
  base := (76057597401401544073437206944358176064299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-26346425868015316050176752013359755000000000000)
      constant := (823220090820490558696044519641830756420652512333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree116.table
  base := (76057597399003133775277150485377826898653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1811434655908119935987035668465000000000000)
      constant := (56658171212442335926940743572812934364871713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535581994247713929477/100000000000000000000)
  centralHi := (267790997123856964739/50000000000000000000)
  directionLo := (134476392823266082781/25000000000000000000)
  directionHi := (4303244570344514649/800000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree117.table
  base := (78279751149011726260131516568405393247321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-26573435158766926329404469961685535000000000000)
      constant := (837744443976933622811195599399351234377053600207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree117.table
  base := (78279751146972815914266539517610714099351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-609014189638861441053116486835000000000000)
      constant := (19219256984137770757370715139708274998695457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134476392823266082781/25000000000000000000)
  centralHi := (4303244570344514649/800000000000000000)
  directionLo := (67527394289960846487/12500000000000000000)
  directionHi := (540219154319686771897/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree118.table
  base := (16106239299047796923935409110690884065543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3828634921359790944090312558573045000000000000)
      constant := (121770933408611981357152130897982297534334918915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree118.table
  base := (80531196493505802342575357221851119952953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1842650481925048710331663252545000000000000)
      constant := (58666161389434742210163800587188873519012013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67527394289960846487/12500000000000000000)
  centralHi := (540219154319686771897/100000000000000000000)
  directionLo := (542522871185756728377/100000000000000000000)
  directionHi := (271261435592878364189/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree119.table
  base := (82811933439837113478869532265267148105629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-3861064820038592412551415122619585000000000000)
      constant := (123882337210066573884653403262041316796401980349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree119.table
  base := (82811933438363911993248999486042469753457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-265465484990501871071996720655000000000000)
      constant := (8526191789071660562669951770093127409260371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542522871185756728377/100000000000000000000)
  centralHi := (271261435592878364189/50000000000000000000)
  directionLo := (136204211761557878733/25000000000000000000)
  directionHi := (544816847046231514933/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree120.table
  base := (21280490495654485656560648775755468683699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-27254463031021757167087623806662875000000000000)
      constant := (882083923807422529647672877941652189572034368532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree120.table
  base := (17024392396273160927034896072431924033271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-89231728949617975460775754125000000000000)
      constant := (2890919731171911872039826577362159620166355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136204211761557878733/25000000000000000000)
  centralHi := (544816847046231514933/100000000000000000000)
  directionLo := (5471012044321932057/1000000000000000000)
  directionHi := (547101204432193205701/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree121.table
  base := (43730641061720826907572465052211649481657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-227119605965069152448887121942055000000000000)
      constant := (7414208461744716157516845060738230176480294478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree121.table
  base := (21865320530594368689134664089331422511891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1889474220950441871848604628665000000000000)
      constant := (61744076882757504216855811775698839490998844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5471012044321932057/1000000000000000000)
  centralHi := (547101204432193205701/100000000000000000000)
  directionLo := (5493760633272222389/1000000000000000000)
  directionHi := (549376063327222238901/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree122.table
  base := (89829893862208640777742353186663510148343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-27708481612524977725543059703314435000000000000)
      constant := (912282260661499937118473091092862276507528394081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree122.table
  base := (8982989386130426269459253087011384210673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1905082133958906259020918420705000000000000)
      constant := (62787630107941700797830294415302390684241330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5493760633272222389/1000000000000000000)
  centralHi := (549376063327222238901/100000000000000000000)
  directionLo := (551641541240936401763/100000000000000000000)
  directionHi := (137910385310234100441/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree123.table
  base := (11528474649856583617593610901668879338417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-27935490903276588004770777651640215000000000000)
      constant := (927573034178570123477707460801198453329358006712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree123.table
  base := (9222779719808414308009521044634617801661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-640230015655790215397744070915000000000000)
      constant := (21279991343387145507668582426959423246116270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551641541240936401763/100000000000000000000)
  centralHi := (137910385310234100441/25000000000000000000)
  directionLo := (138474438319955683019/25000000000000000000)
  directionHi := (553897753279822732077/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree124.table
  base := (47327496066667564739906579549873377965523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-28162500194028198283998495599965995000000000000)
      constant := (942991544422309408832845915180332956320768142282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree124.table
  base := (94654992132682088540226233047108059114871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1936297959975835033365546004785000000000000)
      constant := (64901108649415975817552940669609269241412291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138474438319955683019/25000000000000000000)
  centralHi := (553897753279822732077/100000000000000000000)
  directionLo := (69518101526935393233/12500000000000000000)
  directionHi := (111228962443096629173/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree125.table
  base := (97111478665640214731106118792440302658981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4055644212111401223318030506898825000000000000)
      constant := (136933970198958994245991776726083522360446949061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree125.table
  base := (97111478665085338498400411016068037402573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1951905872984299420537859796825000000000000)
      constant := (65971033965705050709363585640712428785454033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69518101526935393233/12500000000000000000)
  centralHi := (111228962443096629173/20000000000000000000)
  directionLo := (111676565710081656061/20000000000000000000)
  directionHi := (279191414275204140153/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree126.table
  base := (12449657099471358656689559056798068535897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4088074110790202691779133070945365000000000000)
      constant := (139173110727111668070562107075040166453732134856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree126.table
  base := (49798628397649714884395888931827512275343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-93691132666322086081436837565000000000000)
      constant := (3192845237096608451025492233233655024550686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/20000000000000000000)
  centralHi := (279191414275204140153/50000000000000000000)
  directionLo := (5606119105813880991/1000000000000000000)
  directionHi := (560611910581388099101/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree127.table
  base := (25528081630936348452294806814024066224637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-28843528066283029121681649444943335000000000000)
      constant := (990013495513521154917958587245929884129234326316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree127.table
  base := (102112326523344868263230098768096764411133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-283303099857318313554641054415000000000000)
      constant := (9733893812769655246888088501419290293233399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5606119105813880991/1000000000000000000)
  centralHi := (560611910581388099101/100000000000000000000)
  directionLo := (562832164460662218559/100000000000000000000)
  directionHi := (1758850513939569433/312500000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree128.table
  base := (52328343924797299441282567543335654463813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-29070537357034639400909367393269115000000000000)
      constant := (1005942952663940815823419118637403986116873419142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree128.table
  base := (104656687849254340178264830881102425372297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-1998729612009692582054801172945000000000000)
      constant := (69233554096782164889534972076983150932818237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562832164460662218559/100000000000000000000)
  centralHi := (1758850513939569433/312500000000000000)
  directionLo := (113008738850981530647/20000000000000000000)
  directionHi := (141260923563726913309/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree129.table
  base := (107230340773359420660483996566834465881421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-29297546647786249680137085341594895000000000000)
      constant := (1022000146541053176145348616006100626629164454907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree129.table
  base := (10723034077307037707440615811564346294807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-671445841672718989742371654995000000000000)
      constant := (23446214067071135039420369487074504240636490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113008738850981530647/20000000000000000000)
  centralHi := (141260923563726913309/25000000000000000000)
  directionLo := (567246602002156728017/100000000000000000000)
  directionHi := (283623301001078364009/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree130.table
  base := (54916642647544463064126024584955062452231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-29524555938537859959364803289920675000000000000)
      constant := (1038185077144873238948646269335525784161662632354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree130.table
  base := (27458321323710850693120916589681233229217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2029945438026621356399428757025000000000000)
      constant := (71452521002682366314632449966283223591254228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567246602002156728017/100000000000000000000)
  centralHi := (283623301001078364009/50000000000000000000)
  directionLo := (569440987766733239101/100000000000000000000)
  directionHi := (284720493883366619551/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree131.table
  base := (11246552141483864550609726912837642806591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-29751565229289470238592521238246455000000000000)
      constant := (1054497744475417983542160526234355602780429102970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree131.table
  base := (2811638035365752534332505663767192104667/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2045553351035085743571742549065000000000000)
      constant := (72575190501190238844765856881909441367920280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569440987766733239101/100000000000000000000)
  centralHi := (284720493883366619551/50000000000000000000)
  directionLo := (571626949692290550297/100000000000000000000)
  directionHi := (285813474846145275149/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree132.table
  base := (23025409826533835999162297728531074629863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (256111663457074716782058133020000000000000)
      linear := (-35393830602173648781369821944005000000000000)
      constant := (1264389785752899574703140106090928589706902715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree132.table
  base := (115127049132492055292735798304838527081271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-687053754681183376914685447035000000000000)
      constant := (24568883565579438646464936119993869689568897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571626949692290550297/100000000000000000000)
  centralHi := (285813474846145275149/50000000000000000000)
  directionLo := (286902292026515583239/50000000000000000000)
  directionHi := (573804584053031166479/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree133.table
  base := (117817868448645041018038560426456601202521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85843521546554129447725856220000000000000)
      linear := (-11953139616459315709160252130945000000000000)
      constant := (430354685127327595214246026562018748745505041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree133.table
  base := (117817868448494610278450750258100905969711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-296681311007430645416624304735000000000000)
      constant := (10692414512761138551317167448839302717909133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286902292026515583239/50000000000000000000)
  centralHi := (573804584053031166479/100000000000000000000)
  directionLo := (115194797060636683259/20000000000000000000)
  directionHi := (71996748162897927037/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree134.table
  base := (120537979362833684037409723088238208445379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-30432593101544301076275675083223795000000000000)
      constant := (1104202166827591289195734543959562597281718200693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree134.table
  base := (120537979362705931174884593260069325772061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-298911012865782700726954846455000000000000)
      constant := (10856563311280090295139311136490207977316183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115194797060636683259/20000000000000000000)
  centralHi := (71996748162897927037/12500000000000000000)
  directionLo := (578135246124807186729/100000000000000000000)
  directionHi := (57813524612480718673/10000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree135.table
  base := (4931495275012188235992972227241663014099/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-30659602392295911355503393031549575000000000000)
      constant := (1121025781065230588460344274517601476870800223325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree135.table
  base := (30821845468799054482802882108120127055681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-702661667689647764086999239075000000000000)
      constant := (25717925155212592252864161341402363557559068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578135246124807186729/100000000000000000000)
  centralHi := (57813524612480718673/10000000000000000000)
  directionLo := (145072114368499292151/25000000000000000000)
  directionHi := (116057691494799433721/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree136.table
  base := (63033037993064589757603395694234348215149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-30886611683047521634731110979875355000000000000)
      constant := (1137977132029696462650677780245938447901402928566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree136.table
  base := (126066075986037056171457062442353846534387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2123592916077407679433311509265000000000000)
      constant := (78320398449360907235176625988209430777222127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145072114368499292151/25000000000000000000)
  centralHi := (116057691494799433721/20000000000000000000)
  directionLo := (72804213578193597743/12500000000000000000)
  directionHi := (116486741725109756389/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree137.table
  base := (64437030847689551927331883463105471734719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-31113620973799131913958828928201135000000000000)
      constant := (1155056219721010926676133408844870314051819648946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree137.table
  base := (128874061695300880709560937427484191130379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2139200829085872066605625301305000000000000)
      constant := (79495812130131544626820338432332168013737959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72804213578193597743/12500000000000000000)
  centralHi := (116486741725109756389/20000000000000000000)
  directionLo := (584571087216148840883/100000000000000000000)
  directionHi := (146142771804037210221/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree138.table
  base := (131711339003126950714935771325923137778919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-31340630264550742193186546876526915000000000000)
      constant := (1172263044139196140020585124712489075069246725873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree138.table
  base := (65855669501530266907386469477970554542553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-718269580698112151259313031115000000000000)
      constant := (26893338835983739540392622284501587763595742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584571087216148840883/100000000000000000000)
  centralHi := (146142771804037210221/25000000000000000000)
  directionLo := (586700679286150078659/100000000000000000000)
  directionHi := (29335033964307503933/5000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree139.table
  base := (134577907909445292638011486861695757900139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4509662793614621781773466403550385000000000000)
      constant := (169942515040610613281782740180242364900835971659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree139.table
  base := (134577907909388902915444159754734751514587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2170416655102800840950252885385000000000000)
      constant := (81873011582821459854244584198994429781806327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586700679286150078659/100000000000000000000)
  centralHi := (29335033964307503933/5000000000000000000)
  directionLo := (588822569319985873417/100000000000000000000)
  directionHi := (294411284659992936709/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree140.table
  base := (27494753682881299769239640641506393472337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4542092692293423250234568967596925000000000000)
      constant := (172437129022323930521687544504891953866325762485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree140.table
  base := (27494753682871724971428541915326175155421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-312289224015895032588938096775000000000000)
      constant := (11867828193534827671396774396229892627331315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588822569319985873417/100000000000000000000)
  centralHi := (294411284659992936709/50000000000000000000)
  directionLo := (59093684028527888553/10000000000000000000)
  directionHi := (590936840285278885531/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree141.table
  base := (35099730129520622033914301810991641703551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-32021658136805573030869700721504255000000000000)
      constant := (1224649937755197792453131863735730927735078714468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree141.table
  base := (140398920518041845875772914015731380954189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-104839641958082362633089546165000000000000)
      constant := (4013589229700939772796684162610731380954189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59093684028527888553/10000000000000000000)
  centralHi := (590936840285278885531/100000000000000000000)
  directionLo := (593043573670694827753/100000000000000000000)
  directionHi := (296521786835347413877/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree142.table
  base := (71676682110272264712889158047279692020761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-32248667427557183310097418669830035000000000000)
      constant := (1242367709081086921060111404078577824180224057374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree142.table
  base := (17919170527563753521050016472602121401343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2217240394128194002467194261505000000000000)
      constant := (85504740989750785147241796655527156395425624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593043573670694827753/100000000000000000000)
  centralHi := (296521786835347413877/50000000000000000000)
  directionLo := (297571424761295116163/50000000000000000000)
  directionHi := (595142849522590232327/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree143.table
  base := (36584274880465770534870847501307533484279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-268394022465361930490290385274015000000000000)
      constant := (10414985265569887963959669264500814048459092132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree143.table
  base := (146337099521833795394648579249262102998837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2232848307136658389639508053545000000000000)
      constant := (86732898852838426552163817039639504162975577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297571424761295116163/50000000000000000000)
  centralHi := (595142849522590232327/100000000000000000000)
  directionLo := (298617373240250423107/50000000000000000000)
  directionHi := (119446949296100169243/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree144.table
  base := (29870025284421533966834617118330820589643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-32702686009060403868552854566481595000000000000)
      constant := (1278186461913827618199733321085198140096166855905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree144.table
  base := (149350126422082810662697823451542902451203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-749485406715040925603940615195000000000000)
      constant := (29323282470994707456256066491600800317158421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298617373240250423107/50000000000000000000)
  centralHi := (119446949296100169243/20000000000000000000)
  directionLo := (599319341811515169709/100000000000000000000)
  directionHi := (59931934181151516971/10000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree145.table
  base := (15239244492134678155126520423320587566313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-32929695299812014147780572514807375000000000000)
      constant := (1296287443420721386430678621194743973483888270710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree145.table
  base := (19049055615165710197769010964676295654351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2264064133153587163984135637625000000000000)
      constant := (89215586670189313356856632650940617669930968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599319341811515169709/100000000000000000000)
  centralHi := (59931934181151516971/10000000000000000000)
  directionLo := (1503491778608939119/250000000000000000)
  directionHi := (601396711443575647601/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree146.table
  base := (155464055019647796235040067292079570268273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4736672084366232061001184351876165000000000000)
      constant := (187788023093522621512801663193598572708888432913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree146.table
  base := (155464055019629887831803796503567427384403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2279672046162051551156449429665000000000000)
      constant := (90470116624455416589683757481644915975072463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1503491778608939119/250000000000000000)
  centralHi := (601396711443575647601/100000000000000000000)
  directionLo := (2413867719990992479/400000000000000000)
  directionHi := (603466929997748119751/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree147.table
  base := (6342598268683077052594563222933210444251/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4769101983045033529462286915922705000000000000)
      constant := (190410373802236965178917494624332931635383198275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree147.table
  base := (158564956717061727419175697214269700927727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-109299045674786473253750629605000000000000)
      constant := (4368258917894467825019407222019269700927727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2413867719990992479/400000000000000000)
  centralHi := (603466929997748119751/100000000000000000000)
  directionLo := (151382517704874583271/25000000000000000000)
  directionHi := (121106014163899666617/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree148.table
  base := (40423787503424794292690414511626960081081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-33610723172066844985463726359784715000000000000)
      constant := (1351356808303742479919145006226392872812447576508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree148.table
  base := (32339030002737255684456990254834920095311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-330126838882711475071582430535000000000000)
      constant := (13286506946310843314809482226162523801429665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151382517704874583271/25000000000000000000)
  centralHi := (121106014163899666617/20000000000000000000)
  directionLo := (607586206009012604093/100000000000000000000)
  directionHi := (303793103004506302047/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree149.table
  base := (164854634909578319729247155716026798442941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-33837732462818455264691444308110495000000000000)
      constant := (1369968736718929020634666789015778868579502740747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree149.table
  base := (3297092698191347470410161742453979179549/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2326495785187444712673390805785000000000000)
      constant := (94286450669632993710727136341071678138526450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607586206009012604093/100000000000000000000)
  centralHi := (303793103004506302047/50000000000000000000)
  directionLo := (152408851612649523681/25000000000000000000)
  directionHi := (24385416258023923789/4000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree150.table
  base := (168043411404776873879900220371498679889533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-34064741753570065543919162256436275000000000000)
      constant := (1388708401861237494918064910598407661853782836811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree150.table
  base := (84021705702383792528026826412748832552539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-780701232731969699948568199275000000000000)
      constant := (31858714470718803288592071148528483655735546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152408851612649523681/25000000000000000000)
  centralHi := (24385416258023923789/4000000000000000000)
  directionLo := (122335548368239324001/20000000000000000000)
  directionHi := (305838870920598310003/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree151.table
  base := (34252295899871220155300926434035773908647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-34291751044321675823146880204762055000000000000)
      constant := (1407575803730686634408548376081622759903626336245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree151.table
  base := (85630739749674109366636401303812543095071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2357711611204373487018018389865000000000000)
      constant := (96874626851747439088604981135405126809992982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/20000000000000000000)
  centralHi := (305838870920598310003/50000000000000000000)
  directionLo := (15342832017951110959/2500000000000000000)
  directionHi := (613713280718044438361/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree152.table
  base := (174508839193376002400739907810240605470703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8470000000000000000000000000000000000000000
      center := (123662)
      previous := (61831)
      next := (61831)
      square := (600904650825878906134080993540000000000000)
      linear := (-95619834723194698344527972723235000000000000)
      constant := (3951720061848462010338086942514333792833685441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree152.table
  base := (174508839193369314370727098199447744548477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2373319524212837874190332181905000000000000)
      constant := (98181900988407342215403232206868402635518017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15342832017951110959/2500000000000000000)
  centralHi := (613713280718044438361/100000000000000000000)
  directionLo := (615742090485509080897/100000000000000000000)
  directionHi := (307871045242754540449/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree153.table
  base := (177785490486895327030742475842441470015403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-4963681375117842340228902300201945000000000000)
      constant := (206527688235868558881904126063606053351742818443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree153.table
  base := (177785490486889652379745149881781491517381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-796309145740434087120881991315000000000000)
      constant := (33165988607379117878269622491957470440621667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615742090485509080897/100000000000000000000)
  centralHi := (307871045242754540449/50000000000000000000)
  directionLo := (123552847488226590009/20000000000000000000)
  directionHi := (308882118720566475023/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree154.table
  base := (22636429172496447434899660432760475178933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (256111663457074716782058133020000000000000)
      linear := (-41290175816501188501570288134285000000000000)
      constant := (1729568393981180161518827748433757252316758504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree154.table
  base := (90545716689983382430425103449226569703587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-343505050032823806933565680855000000000000)
      constant := (14403260193276954502990410739505359418221522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123552847488226590009/20000000000000000000)
  centralHi := (308882118720566475023/50000000000000000000)
  directionLo := (15494494670022803921/2500000000000000000)
  directionHi := (619779786800912156841/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree155.table
  base := (184426667872661035152602670133360136805931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-35199788207328116940057751998065175000000000000)
      constant := (1484322778480251046793622825445072316450739104077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree155.table
  base := (23053333484082118799053596947739034354507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-345734751891175862243896222575000000000000)
      constant := (14593781082973215449131624563120736824508168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15494494670022803921/2500000000000000000)
  centralHi := (619779786800912156841/100000000000000000000)
  directionLo := (621788802723837866453/100000000000000000000)
  directionHi := (310894401361918933227/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree156.table
  base := (187791193965018757140550471143024927299861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-35426797498079727219285469946390955000000000000)
      constant := (1503828863985671098610571276710407192945696598387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree156.table
  base := (93895596982507645869905512693175641879719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-811917058748898474293195783355000000000000)
      constant := (34499634835253330080615430443444458986316066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621788802723837866453/100000000000000000000)
  centralHi := (310894401361918933227/50000000000000000000)
  directionLo := (623791348335726279781/100000000000000000000)
  directionHi := (311895674167863139891/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree157.table
  base := (95592505828549307837990324079655318003829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-35653806788831337498513187894716735000000000000)
      constant := (1523462686218336223996807809978807457740153563686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree157.table
  base := (7647400466283827033686384576563169154563/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2451359089255159810051901142105000000000000)
      constant := (104850132127782259440430049162150663806145575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623791348335726279781/100000000000000000000)
  centralHi := (311895674167863139891/50000000000000000000)
  directionLo := (312893742876181145977/50000000000000000000)
  directionHi := (125157497150472458391/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree158.table
  base := (48652030237238327354591565389144542677361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-35880816079582947777740905843042515000000000000)
      constant := (1543224245178262536463343524501760322523314563548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree158.table
  base := (194608120948950815543100164024623536789513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2466967002263624197224214934145000000000000)
      constant := (106210150446880422709388783485847094272579773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312893742876181145977/50000000000000000000)
  centralHi := (125157497150472458391/20000000000000000000)
  directionLo := (627777276101980833507/100000000000000000000)
  directionHi := (156944319025495208377/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree159.table
  base := (198060521840634388104997667089042045254231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-36107825370334558056968623791368295000000000000)
      constant := (1563113540865465798218700480487164696551250450177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree159.table
  base := (198060521840632272622147057744645870428893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-827524971757362861465509575395000000000000)
      constant := (35859653154351854282030765451827521093002251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627777276101980833507/100000000000000000000)
  centralHi := (156944319025495208377/25000000000000000000)
  directionLo := (125952155909421782779/20000000000000000000)
  directionHi := (78720097443388614237/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree160.table
  base := (100771107166096138096888140791865099379531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-5190690665869452619456620248527725000000000000)
      constant := (226161510468565918199728260064852918811994587222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree160.table
  base := (201542214332190481760439670257231709746037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2498182828280552971568842518225000000000000)
      constant := (108956559176308738978844514639401865904666777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125952155909421782779/20000000000000000000)
  centralHi := (78720097443388614237/12500000000000000000)
  directionLo := (12634761106115808949/2000000000000000000)
  directionHi := (631738055305790447451/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree161.table
  base := (25631649802959537148320887703186763626897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-5223120564548254087917722812574265000000000000)
      constant := (229039334631680643642961471258991115675891902856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree161.table
  base := (205053198423674775138428950394674273309203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-359112963041288194105879472895000000000000)
      constant := (15763278512377283869062129751869022819927609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12634761106115808949/2000000000000000000)
  centralHi := (631738055305790447451/100000000000000000000)
  directionLo := (633709161672215046177/100000000000000000000)
  directionHi := (316854580836107523089/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree162.table
  base := (20859347411513469837719119337024945316807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-36788853242589388894651777636345635000000000000)
      constant := (1623547848290889784956887701499362699546841259690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree162.table
  base := (208593474115133407416898647962696026288951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-120447554966546749805403338205000000000000)
      constant := (5320863366383491452749520760592696026288951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633709161672215046177/100000000000000000000)
  centralHi := (316854580836107523089/50000000000000000000)
  directionLo := (635674156036771109889/100000000000000000000)
  directionHi := (63567415603677110989/10000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree163.table
  base := (53040760351653668953561477356527084075487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-37015862533340999173879495584671415000000000000)
      constant := (1643948090887351696760761495228169715166037734116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree163.table
  base := (212163041406613580897716936065753611431403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2545006567305946133085783894345000000000000)
      constant := (113142102498546730500098829402685825840059463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635674156036771109889/100000000000000000000)
  centralHi := (63567415603677110989/10000000000000000000)
  directionLo := (637633094905542729607/100000000000000000000)
  directionHi := (79704136863192841201/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree164.table
  base := (10788095014908119965376899902993440853929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-37242871824092609453107213532997195000000000000)
      constant := (1664476070211164358116586859996652898591666170860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree164.table
  base := (107880950149080735349190184077008246389581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2560614480314410520258097686385000000000000)
      constant := (114554865000122186737979016176254346348362402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637633094905542729607/100000000000000000000)
  centralHi := (79704136863192841201/12500000000000000000)
  directionLo := (159896508479817285781/25000000000000000000)
  directionHi := (1023337654270830629/160000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree165.table
  base := (70204816252743371948542730348183496003/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 25270000000000000000000000000000000000000000
      center := (368942)
      previous := (184471)
      next := (184471)
      square := (1792781644199523017474406931140000000000000)
      linear := (-309668438965654708531693648605975000000000000)
      constant := (13926708977374723802112717381864874044998690625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree165.table
  base := (43878010157964449961180308613955732282413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (1022)
      previous := (511)
      next := (511)
      square := (4966154139056850463918024740000000000000)
      linear := (-858740797774291635810137159475000000000000)
      constant := (38658806066260212618035920289613450629884455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159896508479817285781/25000000000000000000)
  centralHi := (1023337654270830629/160000000000000000)
  directionLo := (160383256967946185001/25000000000000000000)
  directionHi := (128306605574356948001/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree166.table
  base := (223047492881640781767498600012116237435959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-37696890405595830011562649429648755000000000000)
      constant := (1705915239040896874989847593796140810572080875553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree166.table
  base := (111523746440820056950944305750985300451867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2591830306331339294602725270465000000000000)
      constant := (117406762094523011957798834644911382618978414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160383256967946185001/25000000000000000000)
  centralHi := (128306605574356948001/20000000000000000000)
  directionLo := (643474130727956905363/100000000000000000000)
  directionHi := (160868532681989226341/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree167.table
  base := (22673422657365887223395972661447266132591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-5417699956621062898684338196853505000000000000)
      constant := (246689489792406209167811435830444922819377074710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree167.table
  base := (226734226573658305872597394357428500287249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 210000000000000000000000000000000000000000
      center := (3066)
      previous := (1533)
      next := (1533)
      square := (14898462417170551391754074220000000000000)
      linear := (-2607438219339803681775039062505000000000000)
      constant := (118845896687350217149663609743510998506032229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643474130727956905363/100000000000000000000)
  centralHi := (160868532681989226341/25000000000000000000)
  directionLo := (645409395641138315797/100000000000000000000)
  directionHi := (322704697820569157899/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree168.table
  base := (28806281483239952525370721026274422932617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30989511278306040730629034095420000000000000)
      linear := (-5450129855299864367145440760900045000000000000)
      constant := (249695050682884897865666742455930524544957145416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree168.table
  base := (57612562966479784984000758866952713996387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (709450591293835780559717820000000000000)
      linear := (-124906958683250860426064421645000000000000)
      constant := (5728277237012530572775217342147810855985548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell119.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645409395641138315797/100000000000000000000)
  centralHi := (322704697820569157899/50000000000000000000)
  directionLo := (161834718742537413773/25000000000000000000)
  directionHi := (647338874970149655093/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree169.table
  base := (117097784379232216289429310642389225698687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3057670000000000000000000000000000000000000000
      center := (44641982)
      previous := (22320991)
      next := (22320991)
      square := (216926578948142285114403238667940000000000000)
      linear := (-38377918277850660849245803274626095000000000000)
      constant := (1769032017740961998509728941594018505248420855858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree169.table
  base := (46839113751692805066625012923862485475729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (438)
      previous := (219)
      next := (219)
      square := (2128351773881507341679153460000000000000)
      linear := (-376950577908104636588523806655000000000000)
      constant := (17392933994894665169672586870742937282135935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell119.Kernel169
