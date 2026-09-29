import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell228.Parameters
import ForestUnimodality.BinomialMassData.Q107_180.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_180.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_180.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_180.Batch150_199
import ForestUnimodality.BinomialMassData.Q3_5.Batch000_049
import ForestUnimodality.BinomialMassData.Q3_5.Batch050_099
import ForestUnimodality.BinomialMassData.Q3_5.Batch100_149
import ForestUnimodality.BinomialMassData.Q3_5.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree000.table
  base := (391865145196855783643385957/25000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-65002516274864816092637910000000000000000)
      constant := (9404763484724538807441262968000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree000.table
  base := (391865145196855783643385957/25000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-5416876356238734674386492500000000000000)
      constant := (783730290393711567286771914000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree001.table
  base := (85347409372246782457192279706108410493827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-2404771907334386746302179491140000000000000)
      constant := (139499200026381076012723615700401124999999740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree001.table
  base := (21171184707601432528040019335624324845679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-7440876256279347483735264840000000000000)
      constant := (427281019935784075208236913914486496913580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48989794855663561963/100000000000000000000)
  directionHi := (12247448713915890491/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree002.table
  base := (50043315467190830275879180931306037808641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-3054475875247423458103135412280000000000000)
      constant := (83929177657791138178639086503737781249998420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree002.table
  base := (12348929247715055581280140965835865162037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-9464876156319960293084037180000000000000)
      constant := (255907636461836328606085137124717303240740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48989794855663561963/100000000000000000000)
  centralHi := (12247448713915890491/25000000000000000000)
  directionLo := (69282032302755091741/100000000000000000000)
  directionHi := (34641016151377545871/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree003.table
  base := (31762829766794646236137071692267396145847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-411575538128940018878232370380000000000000)
      constant := (6258179277223271222385569844113631306252460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree003.table
  base := (3908486379916470283156639946454240970027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-11488876056360573102432809520000000000000)
      constant := (171554632367998188325402969676169638801080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69282032302755091741/100000000000000000000)
  centralHi := (34641016151377545871/50000000000000000000)
  directionLo := (5303300858899106433/6250000000000000000)
  directionHi := (84852813742385702929/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree004.table
  base := (2706092899449033489317713460955994707447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-4353883811073496881705047254560000000000000)
      constant := (42333828835781125355269466212077691408513120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree004.table
  base := (10645901898339108246999696646015569230109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-13512875956401185911781581860000000000000)
      constant := (129174721758558987173398655692155692301090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5303300858899106433/6250000000000000000)
  centralHi := (84852813742385702929/100000000000000000000)
  directionLo := (97979589711327123927/100000000000000000000)
  directionHi := (12247448713915890491/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree005.table
  base := (15559349305921403082175955816444509787151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-5003587778986533593506003175700000000000000)
      constant := (35250259234893277829191343725277605855184620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree005.table
  base := (7649487882337101501440884667900322491761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-15536875856441798721130354200000000000000)
      constant := (107925507142391815107684116729003224917610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97979589711327123927/100000000000000000000)
  centralHi := (12247448713915890491/12500000000000000000)
  directionLo := (109544511501033222691/100000000000000000000)
  directionHi := (27386127875258305673/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree006.table
  base := (2886056341203769060389935387563915973687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-628143527433285589478551010760000000000000)
      constant := (3545913318326599790813115600068019501054640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree006.table
  base := (226920419486347788259112803458658273919/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-17560875756482411530479126540000000000000)
      constant := (98090058674485010233536315136664568479750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109544511501033222691/100000000000000000000)
  centralHi := (27386127875258305673/25000000000000000000)
  directionLo := (6/5)
  directionHi := (120000000000000000001/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree007.table
  base := (4333075506889205997420023655035614539529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-6302995714812607017107915017980000000000000)
      constant := (30804413745157788075127667760084891108073960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree007.table
  base := (8507534076521625524185216743163179803437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-19584875656523024339827898880000000000000)
      constant := (95041349609407821550776305613815899017185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6/5)
  centralHi := (120000000000000000001/100000000000000000000)
  directionLo := (129614813968157204619/100000000000000000000)
  directionHi := (6480740698407860231/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree008.table
  base := (6461742506065575196106857332589822223053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-6952699682725643728908870939120000000000000)
      constant := (31173159205820194766246000267147512001345860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree008.table
  base := (6329309656645800450724833401524023333139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-21608875556563637149176671220000000000000)
      constant := (96508352873954694630175759935620116665695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129614813968157204619/100000000000000000000)
  centralHi := (6480740698407860231/5000000000000000000)
  directionLo := (69282032302755091741/50000000000000000000)
  directionHi := (138564064605510183483/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree009.table
  base := (93833164001563456233514338079162246681/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-281570505579210386692956550380000000000000)
      constant := (1208582325464341536152008195753986740043000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree009.table
  base := (457782033352037897711524218677790206583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-23632875456604249958525443560000000000000)
      constant := (101323431562277953394438438295889510329150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69282032302755091741/50000000000000000000)
  centralHi := (138564064605510183483/100000000000000000000)
  directionLo := (146969384566990685891/100000000000000000000)
  directionHi := (36742346141747671473/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree010.table
  base := (1612229823285964477526788797361331527809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-8252107618551717152510782781400000000000000)
      constant := (34967174202533141268583592359000714150101160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree010.table
  base := (1562476006259958464608883964466059822169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-25656875356644862767874215900000000000000)
      constant := (108846015201250376972870964844660598221690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146969384566990685891/100000000000000000000)
  centralHi := (36742346141747671473/25000000000000000000)
  directionLo := (154919333848296675407/100000000000000000000)
  directionHi := (9682458365518542213/6250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree011.table
  base := (396448386083030466736215765935853852273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-8901811586464753864311738702540000000000000)
      constant := (38053307488294614249737949356245916203411300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree011.table
  base := (1894577345773795936214911230550886196247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-27680875256685475577222988240000000000000)
      constant := (118695467051518873511385842594754430981235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154919333848296675407/100000000000000000000)
  centralHi := (9682458365518542213/6250000000000000000)
  directionLo := (162480768092719207209/100000000000000000000)
  directionHi := (16248076809271920721/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree012.table
  base := (182976824209256446405237637294537760643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-1061279506041976730679188291520000000000000)
      constant := (4645436304145768006711711083653083984578700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree012.table
  base := (418739585960297069706419069489719222343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-29704875156726088386571760580000000000000)
      constant := (130625701306276333716513901782897192223430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162480768092719207209/100000000000000000000)
  centralHi := (16248076809271920721/10000000000000000000)
  directionLo := (5303300858899106433/3125000000000000000)
  directionHi := (169705627484771405857/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree013.table
  base := (-1238224988483836255404266378248506069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-10201219522290827287913650544820000000000000)
      constant := (46177707030857780340104367256101874201682200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree013.table
  base := (-80668127171881034269416168348580021139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-31728875056766701195920532920000000000000)
      constant := (144465089874861794722850318296257099894305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5303300858899106433/3125000000000000000)
  centralHi := (169705627484771405857/100000000000000000000)
  directionLo := (35327043465311387419/20000000000000000000)
  directionHi := (22079402165819617137/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree014.table
  base := (-825162476978615638038687816518964743633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-10850923490203863999714606465960000000000000)
      constant := (51118167791679561064308751831317277115314540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree014.table
  base := (-885255289092800011792961495640318806271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-33752874956807314005269305260000000000000)
      constant := (160086679069329404395589543113798405968645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35327043465311387419/20000000000000000000)
  centralHi := (22079402165819617137/12500000000000000000)
  directionLo := (183303027798233600263/100000000000000000000)
  directionHi := (22912878474779200033/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree015.table
  base := (-1543126620828970303852413606877649058501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-1277847495346322301279506931900000000000000)
      constant := (6288715946846122520416732668399523169469820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree015.table
  base := (-159584298250459314720475076017669850037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-35776874856847926814618077600000000000000)
      constant := (177392665546367010964496811649116507498150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183303027798233600263/100000000000000000000)
  centralHi := (22912878474779200033/12500000000000000000)
  directionLo := (189736659610102759919/100000000000000000000)
  directionHi := (2371708245126284499/1250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree016.table
  base := (-2181804225549704399821429731470041217603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-12150331426029937423316518308240000000000000)
      constant := (62593376359200045893911434100426533227483140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree016.table
  base := (-1113947527340718909486322801024361678527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-37800874756888539623966849940000000000000)
      constant := (196305730069603727537232815701756383214730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189736659610102759919/100000000000000000000)
  centralHi := (2371708245126284499/1250000000000000000)
  directionLo := (39191835884530849571/20000000000000000000)
  directionHi := (12247448713915890491/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree017.table
  base := (-34420786626522520333417735452259851143/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-12800035393942974135117474229380000000000000)
      constant := (69082768729285197099612426199476623291867200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree017.table
  base := (-1396914265326993590852432327316290843859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-39824874656929152433315622280000000000000)
      constant := (216763787513886288340756462104837091561410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39191835884530849571/20000000000000000000)
  centralHi := (12247448713915890491/6250000000000000000)
  directionLo := (201990098767241559067/100000000000000000000)
  directionHi := (50497524691810389767/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree018.table
  base := (-408601470178749564141485356499175208879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-498138494883555957293275190760000000000000)
      constant := (2816675704011751346826722117946395899738080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree018.table
  base := (-3303704951131752851700836947959475956907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-41848874556969765242664394620000000000000)
      constant := (238716530175667135293570605708202620215465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201990098767241559067/100000000000000000000)
  centralHi := (50497524691810389767/25000000000000000000)
  directionLo := (207846096908265275223/100000000000000000000)
  directionHi := (25980762113533159403/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree019.table
  base := (-3735494454409442551104853734870240138157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-14099443329769047558719386071660000000000000)
      constant := (83482447345701365031147635286995710976185660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree019.table
  base := (-47071496418006986692012867154018763549/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-43872874457010378052013166960000000000000)
      constant := (262122981068317147863672912060392494580400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207846096908265275223/100000000000000000000)
  centralHi := (25980762113533159403/12500000000000000000)
  directionLo := (26692695630078278027/12500000000000000000)
  directionHi := (213541565040626224217/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree020.table
  base := (-65007120511436889769250344981346764641/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-14749147297682084270520341992800000000000000)
      constant := (91368452321489082748574541744533967442021120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree020.table
  base := (-4186567868821023591500487693409979785433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-45896874357050990861361939300000000000000)
      constant := (286949664935633235256988152332950101072835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26692695630078278027/12500000000000000000)
  centralHi := (213541565040626224217/100000000000000000000)
  directionLo := (109544511501033222691/50000000000000000000)
  directionHi := (219089023002066445383/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree021.table
  base := (-454922408228328960279193747047408736009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-1710983473955013442480144212660000000000000)
      constant := (11077700299038393789645662914084164275183800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree021.table
  base := (-1142931964393342462887111435025088770289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-47920874257091603670710711640000000000000)
      constant := (313169189576114282316370157381498224594220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109544511501033222691/50000000000000000000)
  centralHi := (219089023002066445383/100000000000000000000)
  directionLo := (44899888641287296627/20000000000000000000)
  directionHi := (3507803800100570049/1562500000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree022.table
  base := (-490633602220695921527688911535419729253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-16048555233508157694122253835080000000000000)
      constant := (108467649391458229385639400220788200386101400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree022.table
  base := (-4925686753040695839210297098387566956971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-49944874157132216480059483980000000000000)
      constant := (340759119623044798423291959276062165215145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44899888641287296627/20000000000000000000)
  centralHi := (3507803800100570049/1562500000000000000)
  directionLo := (114891252930760573197/50000000000000000000)
  directionHi := (45956501172304229279/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree023.table
  base := (-2617758075825678676379226337764615782913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-16698259201421194405923209756220000000000000)
      constant := (117667458538806750721543891154052144863361880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree023.table
  base := (-5252121567777515035230717368999826464341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-51968874057172829289408256320000000000000)
      constant := (369701070013652216174030180013000867678295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114891252930760573197/50000000000000000000)
  centralHi := (45956501172304229279/20000000000000000000)
  directionLo := (234946802489414611739/100000000000000000000)
  directionHi := (11747340124470730587/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree024.table
  base := (-5539823564887180287748752120787099695031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-1927551463259359013080462853040000000000000)
      constant := (14143752711185842239228310910610322054894420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree024.table
  base := (-5554046372003617812584054778800459722727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-53992873957213442098757028660000000000000)
      constant := (399979970396837583703713078457997701386365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234946802489414611739/100000000000000000000)
  centralHi := (11747340124470730587/5000000000000000000)
  directionLo := (12/5)
  directionHi := (240000000000000000001/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree025.table
  base := (-5821771226799902412970716605819376015447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-17997667137247267829525121598500000000000000)
      constant := (137342525973941249163960976114510110854975860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree025.table
  base := (-5833932220564270004298944668138191206139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-56016873857254054908105801000000000000000)
      constant := (431583465498374571847197477909309043969305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12/5)
  centralHi := (240000000000000000001/100000000000000000000)
  directionLo := (244948974278317809819/100000000000000000000)
  directionHi := (12247448713915890491/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree026.table
  base := (-1216684738779100350934805003328522734051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-18647371105160304541326077519640000000000000)
      constant := (147810368677073073351737945115756965854186900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree026.table
  base := (-6093805168304062284149419504184843207563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-58040873757294667717454573340000000000000)
      constant := (464501425044040227235613216031075783962185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244948974278317809819/100000000000000000000)
  centralHi := (12247448713915890491/5000000000000000000)
  directionLo := (249799919935935928233/100000000000000000000)
  directionHi := (124899959967967964117/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree027.table
  base := (-6326477231695265265074140084729481478903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-714706484187901527893593831140000000000000)
      constant := (5877576094811983994585061317564731111265820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree027.table
  base := (-3167663247134994980552263040529251358593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-60064873657335280526803345680000000000000)
      constant := (498725542638599573324115058852707486414070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249799919935935928233/100000000000000000000)
  centralHi := (124899959967967964117/50000000000000000000)
  directionLo := (15909902576697319299/6250000000000000000)
  directionHi := (50911688245431421757/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree028.table
  base := (-6552325562909428639056381502919717855993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-19946779040986377964927989361920000000000000)
      constant := (169992825791702150844422889587582057073291340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree028.table
  base := (-6559858417797694053121774723791142748193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-62088873557375893336152118020000000000000)
      constant := (534249007185374405022915454749044286259035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15909902576697319299/6250000000000000000)
  centralHi := (50911688245431421757/20000000000000000000)
  directionLo := (129614813968157204619/50000000000000000000)
  directionHi := (259229627936314409239/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree029.table
  base := (-422632115803352328079804749359798240539/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-20596483008899414676728945283060000000000000)
      constant := (181703327204597476819913721871719529605229120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree029.table
  base := (-1692129488700628329863282404599005944971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-64112873457416506145500890360000000000000)
      constant := (571066233604788028535754582790019881100580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129614813968157204619/50000000000000000000)
  centralHi := (259229627936314409239/100000000000000000000)
  directionLo := (131909059582729191709/50000000000000000000)
  directionHi := (263818119165458383419/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree030.table
  base := (-6956783050104069694770583471948853828163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-2360687441868050154281100133800000000000000)
      constant := (21536059384657348494425835260599206310930660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree030.table
  base := (-6962221065870813190530968173267160034463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-66136873357457118954849662700000000000000)
      constant := (609172642093908616710470555933664199827685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131909059582729191709/50000000000000000000)
  centralHi := (263818119165458383419/100000000000000000000)
  directionLo := (268328157299974763569/100000000000000000000)
  directionHi := (26832815729997476357/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree031.table
  base := (-3568553155871418617210223717490413508193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-21895890944725488100330857125340000000000000)
      constant := (206355195049185109494788907562116560233454680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree031.table
  base := (-7141718851302551093997450186683937081467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-68160873257497731764198435040000000000000)
      constant := (648564477151236382408852575188580314592665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268328157299974763569/100000000000000000000)
  centralHi := (26832815729997476357/10000000000000000000)
  directionLo := (54552726787943423571/20000000000000000000)
  directionHi := (8523863560616159933/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree032.table
  base := (-7303718929091306787765908261542167164459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-22545594912638524812131813046480000000000000)
      constant := (219294279794463781545128999101933689193576420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree032.table
  base := (-3653813614072832685158865942702724205957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-70184873157538344573547207380000000000000)
      constant := (689238659191531633928574859420972757940430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54552726787943423571/20000000000000000000)
  centralHi := (8523863560616159933/3125000000000000000)
  directionLo := (69282032302755091741/25000000000000000000)
  directionHi := (55425625842204073393/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree033.table
  base := (-7457142914994903959017285987578116032927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-2577255431172395724881418774180000000000000)
      constant := (25848993670771395902448008167401439114073140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree033.table
  base := (-932556408005926935408832388140723933741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-72208873057578957382895979720000000000000)
      constant := (731192662876558073950743179452371042650360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69282032302755091741/25000000000000000000)
  centralHi := (55425625842204073393/20000000000000000000)
  directionLo := (281424945589405773273/100000000000000000000)
  directionHi := (140712472794702886637/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree034.table
  base := (-7597807205591924249995875781062307809593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-23845002848464598235733724888760000000000000)
      constant := (246394489900077415512547632604037061348459340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree034.table
  base := (-760060513041090224433447018562322663043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-74232872957619570192244752060000000000000)
      constant := (774424417349300198417966343583883866847850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281424945589405773273/100000000000000000000)
  centralHi := (140712472794702886637/50000000000000000000)
  directionLo := (285657137141713999919/100000000000000000000)
  directionHi := (3570714214271424999/1250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree035.table
  base := (-3863032129532688106703229774431593954881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-24494706816377634947534680809900000000000000)
      constant := (260554349401611864861293929705079135586185560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree035.table
  base := (-7728428463703351469838702802290156035167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-76256872857660183001593524400000000000000)
      constant := (818932224427421878248596663438549219824165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285657137141713999919/100000000000000000000)
  centralHi := (3570714214271424999/1250000000000000000)
  directionLo := (144913767461894385737/50000000000000000000)
  directionHi := (11593101396951550859/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree036.table
  base := (-7842203694105172672703017486872630191193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-931274473492247098493912471520000000000000)
      constant := (10189631568861787125713908033051642188528420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree036.table
  base := (-7844199781592781651666287050332889373639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-78280872757700795810942296740000000000000)
      constant := (864714691522583020983219488540335553131805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144913767461894385737/50000000000000000000)
  centralHi := (11593101396951550859/4000000000000000000)
  directionLo := (293938769133981371783/100000000000000000000)
  directionHi := (36742346141747671473/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree037.table
  base := (-248326984252669252075136697434841800721/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-25794114752203708371136592652180000000000000)
      constant := (290091213236740532161091898115007301050623360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree037.table
  base := (-1589629496821689661862533553353096421569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-80304872657741408620291069080000000000000)
      constant := (911770676634637349024357594704172589460775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293938769133981371783/100000000000000000000)
  centralHi := (36742346141747671473/12500000000000000000)
  directionLo := (148996644257513397193/50000000000000000000)
  directionHi := (297993288515026794387/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree038.table
  base := (-8039039224754244222062798091147518817349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-26443818720116745082937548573320000000000000)
      constant := (305467515227236720881108399133283019515894620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree038.table
  base := (-4020229437275082436591943899026351541799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-82328872557782021429639841420000000000000)
      constant := (960099243247085795219980767697736484582010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148996644257513397193/50000000000000000000)
  centralHi := (297993288515026794387/100000000000000000000)
  directionLo := (301993377410829987889/100000000000000000000)
  directionHi := (30199337741082998789/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree039.table
  base := (-253752861870387917235189852292561257389/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-3010391409781086866082056054940000000000000)
      constant := (35694299777464088165681289541224347157439360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree039.table
  base := (-1015160944575724845983445673593938260249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-84352872457822634238988613760000000000000)
      constant := (1009699623341489022447150916298242469590040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301993377410829987889/100000000000000000000)
  centralHi := (30199337741082998789/10000000000000000000)
  directionLo := (305941170815567089801/100000000000000000000)
  directionHi := (152970585407783544901/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree040.table
  base := (-8189752617506753424966192813423775312033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-27743226655942818506539460415600000000000000)
      constant := (337434547615635285439482899471053483994506540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree040.table
  base := (-2047689874991761536543040905114530823757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-86376872357863247048337386100000000000000)
      constant := (1060571187069388549941825725097709383524860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305941170815567089801/100000000000000000000)
  centralHi := (152970585407783544901/50000000000000000000)
  directionLo := (154919333848296675407/50000000000000000000)
  directionHi := (61967733539318670163/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree041.table
  base := (-2062032714504098255337754225923579914869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-28392930623855855218340416336740000000000000)
      constant := (354024888279727608428234336701760702151648880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree041.table
  base := (-8248978014118634783982616977592567232559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-88400872257903859857686158440000000000000)
      constant := (1112713417883360738824580521674037163837205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154919333848296675407/50000000000000000000)
  centralHi := (61967733539318670163/20000000000000000000)
  directionLo := (313687742827162438683/100000000000000000000)
  directionHi := (78421935706790609671/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree042.table
  base := (-8295315482737682365521772986513460793537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-3226959399085432436682374695320000000000000)
      constant := (41224397279517386121460348038505577057163340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree042.table
  base := (-51850173917708882689241765243562913203/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-90424872157944472667034930780000000000000)
      constant := (1166125892144541306350516521133149669437600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313687742827162438683/100000000000000000000)
  centralHi := (78421935706790609671/25000000000000000000)
  directionLo := (15874507866387543543/5000000000000000000)
  directionHi := (317490157327750870861/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree043.table
  base := (-8331379782515344800796861038763830965969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-29692338559681928641942328179020000000000000)
      constant := (388418490592253433618033478442872093835130220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree043.table
  base := (-333279137141178705522953038436414805683/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-92448872057985085476383703120000000000000)
      constant := (1220808262400839941754566393693448149289625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15874507866387543543/5000000000000000000)
  centralHi := (317490157327750870861/100000000000000000000)
  directionLo := (32124756808418021081/10000000000000000000)
  directionHi := (321247568084180210811/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree044.table
  base := (-2089095997784276673510573448465853680241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-30342042527594965353743284100160000000000000)
      constant := (406221535930782367288582434362589268152038320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree044.table
  base := (-8356886814636769302437275942206103503587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-94472871958025698285732475460000000000000)
      constant := (1276760243675106668561383997360969482482065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32124756808418021081/10000000000000000000)
  centralHi := (321247568084180210811/100000000000000000000)
  directionLo := (162480768092719207209/50000000000000000000)
  directionHi := (324961536185438414419/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree045.table
  base := (-8370377613485276638224007000352015440773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-1147842462796592669094231111900000000000000)
      constant := (15719578938271627266080932747891379073553620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree045.table
  base := (-8370799734334464262404120847192440537393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-96496871858066311095081247800000000000000)
      constant := (1333981602221445796575793889814037797313035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162480768092719207209/50000000000000000000)
  centralHi := (324961536185438414419/100000000000000000000)
  directionLo := (164316767251549834037/50000000000000000000)
  directionHi := (13145341380123986723/4000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree046.table
  base := (-4186700669250008053233532281880435414283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-31641450463421038777345195942440000000000000)
      constant := (443039710883825078718379124407345389257723080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree046.table
  base := (-130839930226783661370847742144881199161/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-98520871758106923904430020140000000000000)
      constant := (1392472146305399316748996596945638016268480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164316767251549834037/50000000000000000000)
  centralHi := (13145341380123986723/4000000000000000000)
  directionLo := (332264954516722994103/100000000000000000000)
  directionHi := (41533119314590374263/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree047.table
  base := (-8365488610998301455450206350217741919821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-32291154431334075489146151863580000000000000)
      constant := (462054720401652293193344696422296758089889980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree047.table
  base := (-8365785671830696030883965971735478422753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-100544871658147536713778792480000000000000)
      constant := (1452231718643692946418710688359322607886235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332264954516722994103/100000000000000000000)
  centralHi := (41533119314590374263/12500000000000000000)
  directionLo := (335857112474933304039/100000000000000000000)
  directionHi := (8396427811873332601/2500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree048.table
  base := (-2086666730796947867126247250889854690627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-3660095377694123577883011976080000000000000)
      constant := (53497068372159908042231642052767304622748560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree048.table
  base := (-4173457976293257940460728989117097243857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-102568871558188149523127564820000000000000)
      constant := (1513260190204814553039595135516829027561430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335857112474933304039/100000000000000000000)
  centralHi := (8396427811873332601/2500000000000000000)
  directionLo := (5303300858899106433/1562500000000000000)
  directionHi := (339411254969542811713/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree049.table
  base := (-51980992974155578393836549049662475893/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-33590562367160148912748063705860000000000000)
      constant := (501296359113895537914839825340032986248534400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree049.table
  base := (-2079291887360239980966640638571519647489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-104592871458228762332476337160000000000000)
      constant := (1575557455125467406381550783230569607050220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5303300858899106433/1562500000000000000)
  centralHi := (339411254969542811713/100000000000000000000)
  directionLo := (342928563989644933747/100000000000000000000)
  directionHi := (85732140997411233437/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree050.table
  base := (-8276383050371308886764634987259059640901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-34240266335073185624549019627000000000000000)
      constant := (521522921593247828980993516609390323381740380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree050.table
  base := (-1034569729389684105943426864010565846407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-106616871358269375141825109500000000000000)
      constant := (1639123426542034283005436955439577366143720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342928563989644933747/100000000000000000000)
  centralHi := (85732140997411233437/25000000000000000000)
  directionLo := (69282032302755091741/20000000000000000000)
  directionHi := (173205080756887729353/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree051.table
  base := (-822495472505822116502164869880995027919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-3876663366998469148483330616460000000000000)
      constant := (60239253115174125877868632119303708949745800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree051.table
  base := (-411255053302503613367828223103450784249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-108640871258309987951173881840000000000000)
      constant := (1703958033172345094834290905091654921575100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69282032302755091741/20000000000000000000)
  centralHi := (173205080756887729353/50000000000000000000)
  directionLo := (87464278422679507063/25000000000000000000)
  directionHi := (349857113690718028253/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree052.table
  base := (-8162686463988431150945356369768166342499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-35539674270899259048150931469280000000000000)
      constant := (563187408090071710801792385565847570525151620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree052.table
  base := (-4081404471490456549076969821751035319621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-110664871158350600760522654180000000000000)
      constant := (1770061216512689067293812989990489646803790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87464278422679507063/25000000000000000000)
  centralHi := (349857113690718028253/100000000000000000000)
  directionLo := (35327043465311387419/10000000000000000000)
  directionHi := (353270434653113874191/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree053.table
  base := (-8089588600661379546703480935518555583659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-36189378238812295759951887390420000000000000)
      constant := (584625295013492468746405894930409439954472420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree053.table
  base := (-8089691070658427924929114315227369603967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-112688871058391213569871426520000000000000)
      constant := (1837432928539324037459055340841863151980165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35327043465311387419/10000000000000000000)
  centralHi := (353270434653113874191/100000000000000000000)
  directionLo := (71330218000508031533/20000000000000000000)
  directionHi := (178325545001270078833/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree054.table
  base := (-2001417408870617664760849287911352415313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-1364410452100938239694549752280000000000000)
      constant := (22461737964302690805841758150495275420324880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree054.table
  base := (-800575533479845718798053749393148530893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-114712870958431826379220198860000000000000)
      constant := (1906073129823670803128525712562342573455350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71330218000508031533/20000000000000000000)
  centralHi := (178325545001270078833/50000000000000000000)
  directionLo := (18/5)
  directionHi := (360000000000000000001/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree055.table
  base := (-1977734140589834495013563456907428176129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-37488786174638369183553799232700000000000000)
      constant := (628712286827981893578572689893377365418684080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree055.table
  base := (-7911008211201404582627237333630752416547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-116736870858472439188568971200000000000000)
      constant := (1975981787986727345825628964381846237917265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18/5)
  centralHi := (360000000000000000001/100000000000000000000)
  directionLo := (7266360849833979997/2000000000000000000)
  directionHi := (363318042491698999851/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree056.table
  base := (-1951348784266081047929361644998019708567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-38138490142551405895354755153840000000000000)
      constant := (651361371064568999064131693521660832288485840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree056.table
  base := (-780545501923758234685621221867831418009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-118760870758513051997917743540000000000000)
      constant := (2047158876431642104360430104378608429099550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7266360849833979997/2000000000000000000)
  centralHi := (363318042491698999851/100000000000000000000)
  directionLo := (366606055596467200527/100000000000000000000)
  directionHi := (22912878474779200033/6250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree057.table
  base := (-3844525048874169745673721831481745277573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-4309799345607160289683967897220000000000000)
      constant := (74934907785569943743861671375152071700073720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree057.table
  base := (-1537820025942923044875393023490174625799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-120784870658553664807266515880000000000000)
      constant := (2119604373304376955014381617710745634355025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366606055596467200527/100000000000000000000)
  centralHi := (22912878474779200033/6250000000000000000)
  directionLo := (73972968035627717403/20000000000000000000)
  directionHi := (46233105022267323377/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree058.table
  base := (-7561905346139151976939820139237584420941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-39437898078377479318956666996120000000000000)
      constant := (697870677523864393151689904855937113238075580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree058.table
  base := (-7561947135338185737053761041254598730923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-122808870558594277616615288220000000000000)
      constant := (2193318260641403485178162179321727006345385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73972968035627717403/20000000000000000000)
  centralHi := (46233105022267323377/12500000000000000000)
  directionLo := (186547581061776300911/50000000000000000000)
  directionHi := (373095162123552601823/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree059.table
  base := (-7423964096435361489978326700144041883551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-40087602046290516030757622917260000000000000)
      constant := (721730888218771965691732604840412152148647380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree059.table
  base := (-3711999495249648766880140189229493955411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-124832870458634890425964060560000000000000)
      constant := (2268300523670766676607403387269705060445890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186547581061776300911/50000000000000000000)
  centralHi := (373095162123552601823/100000000000000000000)
  directionLo := (376297754444535584183/100000000000000000000)
  directionHi := (47037219305566948023/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree060.table
  base := (-3637614498828453593166288621669365253029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-4526367334911505860284286537600000000000000)
      constant := (82888310873715545542486040868399028508909560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree060.table
  base := (-7275258125909199878742538523766326240183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-126856870358675503235312832900000000000000)
      constant := (2344551150238910282980875164581168368799085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376297754444535584183/100000000000000000000)
  centralHi := (47037219305566948023/12500000000000000000)
  directionLo := (379473319220205519839/100000000000000000000)
  directionHi := (2371708245126284499/625000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree061.table
  base := (-7115702234185557685593415141120874961789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-41387009982116589454359534759540000000000000)
      constant := (770662402919169760559878027518349682561901820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree061.table
  base := (-7115726542609260214012366673871039283471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-128880870258716116044661605240000000000000)
      constant := (2422070130340627467088518355272644803582645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379473319220205519839/100000000000000000000)
  centralHi := (2371708245126284499/625000000000000000)
  directionLo := (382622529394179819511/100000000000000000000)
  directionHi := (47827816174272477439/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree062.table
  base := (-3472692804192330571571347592228713806153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-42036713950029626166160490680680000000000000)
      constant := (795733700466132893712524979187320967268064280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree062.table
  base := (-6945405889068119720975875583724681799799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-130904870158756728854010377580000000000000)
      constant := (2500857455733575023023302405569376591001005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382622529394179819511/100000000000000000000)
  centralHi := (47827816174272477439/12500000000000000000)
  directionLo := (38574603043971819983/10000000000000000000)
  directionHi := (385746030439718199831/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree063.table
  base := (-3382140304246906806844752674361231585917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-1580978441405283810294868392660000000000000)
      constant := (30415136596051154212284685196385152209689960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree063.table
  base := (-6764297524410214805433313616525259588211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-132928870058797341663359149920000000000000)
      constant := (2580913119622130768756226073655373702058945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38574603043971819983/10000000000000000000)
  centralHi := (385746030439718199831/100000000000000000000)
  directionLo := (388844441904471613857/100000000000000000000)
  directionHi := (194422220952235806929/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree064.table
  base := (-1643097116106046961977883699271180629449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-43336121885855699589762402522960000000000000)
      constant := (847087363808458470761264734419250749521170480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree064.table
  base := (-1314480514054357639316262613629674197543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-134952869958837954472707922260000000000000)
      constant := (2662237116398113490641306198051258145061425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388844441904471613857/100000000000000000000)
  centralHi := (194422220952235806929/50000000000000000000)
  directionLo := (391918358845308495711/100000000000000000000)
  directionHi := (12247448713915890491/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree065.table
  base := (-6369710193611989748543506649116561998753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-43985825853768736301563358444100000000000000)
      constant := (873369725963118161238829430084168669562020140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree065.table
  base := (-1273944390666238615598581549716571937961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-136976869858878567282056694600000000000000)
      constant := (2744829441428131422760677609707085701550975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391918358845308495711/100000000000000000000)
  centralHi := (12247448713915890491/3125000000000000000)
  directionLo := (98742088290657495087/25000000000000000000)
  directionHi := (394968353162629980349/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree066.table
  base := (-1539061659675687272648637037406402468047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-4959503313520197001484923818360000000000000)
      constant := (100006197021363830769873977906729390223006160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree066.table
  base := (-6156256440191856361521914131104427920203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-139000869758919180091405466940000000000000)
      constant := (2828690090879167430555071226256477860398985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98742088290657495087/25000000000000000000)
  centralHi := (394968353162629980349/100000000000000000000)
  directionLo := (397994974842647981893/100000000000000000000)
  directionHi := (198997487421323990947/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree067.table
  base := (-1186399699704602107362476207756605649363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-45285233789594809725165270286380000000000000)
      constant := (927145504363828415477722538429360994240159700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree067.table
  base := (-1483001666498538269161921487798212235189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-141024869658959792900754239280000000000000)
      constant := (2913819061575519638877090279022035755296220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397994974842647981893/100000000000000000000)
  centralHi := (198997487421323990947/50000000000000000000)
  directionLo := (80199750623053685403/20000000000000000000)
  directionHi := (50124844139408553377/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree068.table
  base := (-1424241588384058115126993487092113857/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-45934937757507846436966226207520000000000000)
      constant := (954638918537429174320635872707075102206640000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree068.table
  base := (-178030411183897311078015923780548175031/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-143048869559000405710103011620000000000000)
      constant := (3000216350881454894071103336243112291995040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80199750623053685403/20000000000000000000)
  centralHi := (50124844139408553377/12500000000000000000)
  directionLo := (201990098767241559067/50000000000000000000)
  directionHi := (80796039506896623627/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree069.table
  base := (-5451150686766269173370268347340583645561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-5176071302824542572085242458740000000000000)
      constant := (109170668325619789941407746534888194943799020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree069.table
  base := (-5451156354268552820745427386990463684029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-145072869459041018519451783960000000000000)
      constant := (3087881956604948127008725185787047681579855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201990098767241559067/50000000000000000000)
  centralHi := (80796039506896623627/20000000000000000000)
  directionLo := (406939798987516088343/100000000000000000000)
  directionHi := (50867474873439511043/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree070.table
  base := (-1038910380199288941774659110829278892973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-47234345693333919860568138049800000000000000)
      constant := (1010836792890766235999596146014232840966918700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree070.table
  base := (-1038911324120566363076267138693657592281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-147096869359081631328800556300000000000000)
      constant := (3176815876918713526990021346332658560192975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406939798987516088343/100000000000000000000)
  centralHi := (50867474873439511043/12500000000000000000)
  directionLo := (12808688457449497979/3125000000000000000)
  directionHi := (409878030638383935329/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree071.table
  base := (-985434066581626938134951442817117446127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-47884049661246956572369093970940000000000000)
      constant := (1039541251872569725391089677642406848686371300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree071.table
  base := (-123179356558862455292809918131730122733/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-149120869259122244138149328640000000000000)
      constant := (3267018110295416357648451006655653975453400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12808688457449497979/3125000000000000000)
  centralHi := (409878030638383935329/100000000000000000000)
  directionLo := (206397674405502931771/50000000000000000000)
  directionHi := (412795348811005863543/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree072.table
  base := (-2324503132352189545489104900710608195747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-1797546430709629380895187033040000000000000)
      constant := (39579607089585913070080761192970727016510360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree072.table
  base := (-4649009535632029118553470135338522072101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-151144869159162856947498100980000000000000)
      constant := (3358488655454514233439939868491307389639495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206397674405502931771/50000000000000000000)
  centralHi := (412795348811005863543/100000000000000000000)
  directionLo := (207846096908265275223/50000000000000000000)
  directionHi := (415692193816530550447/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree073.table
  base := (-4360059933666769720505836676413312908927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-49183457597073029995971005813220000000000000)
      constant := (1098161211145119839769498832674019933087538260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree073.table
  base := (-4360062655909683654084112373291122766677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-153168869059203469756846873320000000000000)
      constant := (3451227511318635858773590149591544386166615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207846096908265275223/50000000000000000000)
  centralHi := (415692193816530550447/100000000000000000000)
  directionLo := (209284495364563497327/50000000000000000000)
  directionHi := (83713798145825398931/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree074.table
  base := (-2030165770006963167144820605219381836501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-49833161564986066707771961734360000000000000)
      constant := (1128076710727116122019892673572207202849736760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree074.table
  base := (-1015083451296839260417006793744037446427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-155192868959244082566195645660000000000000)
      constant := (3545234676977781757532583331277119251071460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209284495364563497327/50000000000000000000)
  centralHi := (83713798145825398931/20000000000000000000)
  directionLo := (26339134382131847121/6250000000000000000)
  directionHi := (421426150114109553937/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree075.table
  base := (-3749821253364200137728555679219535127851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-5609207281433233713285879739500000000000000)
      constant := (128710654432225196743401756068677983676986820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree075.table
  base := (-1874911568933690785513743403138346178319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-157216868859284695375544418000000000000000)
      constant := (3640510151659940268268308052218616538216810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26339134382131847121/6250000000000000000)
  centralHi := (421426150114109553937/100000000000000000000)
  directionLo := (5303300858899106433/1250000000000000000)
  directionHi := (424264068711928514641/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree076.table
  base := (-1714264609025640458815060071083432318633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-51132569500812140131373873576640000000000000)
      constant := (1189118748400031208327040010915457679287629080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree076.table
  base := (-685706157115797054870911328032575583947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-159240868759325308184893190340000000000000)
      constant := (3737053934706965250819803985551185610401325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5303300858899106433/1250000000000000000)
  centralHi := (424264068711928514641/100000000000000000000)
  directionLo := (26692695630078278027/6250000000000000000)
  directionHi := (427083130081252448433/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree077.table
  base := (-387056944687130637575650338056415052763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-51782273468725176843174829497780000000000000)
      constant := (1220245286057185995118055686133898360916191520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree077.table
  base := (-619291372227919908503755389286530457563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-161264868659365920994241962680000000000000)
      constant := (3834866025554769548232723429925836738560925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26692695630078278027/6250000000000000000)
  centralHi := (427083130081252448433/100000000000000000000)
  directionLo := (26867731575255846299/6250000000000000000)
  directionHi := (85976741040818708157/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree078.table
  base := (-2753600377809550404444372975127019490381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-5825775270737579283886198379880000000000000)
      constant := (139086166965510675284538011945195136491731420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree078.table
  base := (-1376800730904080503918394954682126538931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-163288868559406533803590735020000000000000)
      constant := (3933946423717058477345483174421178734610690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26867731575255846299/6250000000000000000)
  centralHi := (85976741040818708157/20000000000000000000)
  directionLo := (216333076527839357587/50000000000000000000)
  directionHi := (17306646122227148607/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree079.table
  base := (-2399963770744148153380935130302925950637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-53081681404551250266776741340060000000000000)
      constant := (1283709398148617786510141322268734759959968060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree079.table
  base := (-2399964671957635462803517239400568938053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-165312868459447146612939507360000000000000)
      constant := (4034295128771967209195608610484997155309735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216333076527839357587/50000000000000000000)
  centralHi := (17306646122227148607/4000000000000000000)
  directionLo := (217715410570772412651/50000000000000000000)
  directionHi := (435430821141544825303/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree080.table
  base := (-50888645403527201171377710655252840263/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-53731385372464286978577697261200000000000000)
      constant := (1316046972304909917452860175224739615950957600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree080.table
  base := (-2035546565271099175611483356908923018341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-167336868359487759422288279700000000000000)
      constant := (4135912140351080362442137116015455384908295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217715410570772412651/50000000000000000000)
  centralHi := (435430821141544825303/100000000000000000000)
  directionLo := (87635609200826578153/20000000000000000000)
  directionHi := (219089023002066445383/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree081.table
  base := (-415086645983195033261411109374513943181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-2014114420013974951495505673420000000000000)
      constant := (49955119446117850596701818104586616653636560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree081.table
  base := (-1660347206546941103242071582719671105459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-169360868259528372231637052040000000000000)
      constant := (4238797458130405992300161774408401644472705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87635609200826578153/20000000000000000000)
  centralHi := (219089023002066445383/50000000000000000000)
  directionLo := (17636326148038882307/4000000000000000000)
  directionHi := (110227038425243014419/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree082.table
  base := (-1274366135797272673748537837527133311369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-55030793308290360402179609103480000000000000)
      constant := (1381933156269515494300298551695188044035582220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree082.table
  base := (-1274366653183356434969252203737969410397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-171384868159568985040985824380000000000000)
      constant := (4342951081822953122823312734229310152948015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17636326148038882307/4000000000000000000)
  centralHi := (110227038425243014419/25000000000000000000)
  directionLo := (221810730128188343241/50000000000000000000)
  directionHi := (443621460256376686483/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree083.table
  base := (-877604526520859744297854006919283032471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-55680497276203397113980565024620000000000000)
      constant := (1415481765889156705618867377922180261487396980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree083.table
  base := (-109700619549959924493647587995239024703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-173408868059609597850334596720000000000000)
      constant := (4448373011172625082885809218058190439011880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221810730128188343241/50000000000000000000)
  centralHi := (443621460256376686483/100000000000000000000)
  directionLo := (446318272088427945867/100000000000000000000)
  directionHi := (111579568022106986467/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree084.table
  base := (-470061805121520674038771480665325489937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-6258911249346270425086835660640000000000000)
      constant := (161048228202744052617012930919792241411811340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree084.table
  base := (-470062162241752566647889496259370759771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-175432867959650210659683369060000000000000)
      constant := (4555063245949192659585321063830703146201145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446318272088427945867/100000000000000000000)
  centralHi := (111579568022106986467/25000000000000000000)
  directionLo := (44899888641287296627/10000000000000000000)
  directionHi := (448998886412872966271/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree085.table
  base := (-12934503943920217979162172533682110719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-56979905212029470537582476866900000000000000)
      constant := (1483790020004568988940554072104219239922540880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree085.table
  base := (-51738312410042174989008550074176395111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-177456867859690823469032141400000000000000)
      constant := (4663021785944153521782230121699629118024445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44899888641287296627/10000000000000000000)
  centralHi := (448998886412872966271/100000000000000000000)
  directionLo := (225831795812724298497/50000000000000000000)
  directionHi := (90332718325089719399/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree086.table
  base := (377366801416786338404369436647475801659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-57629609179942507249383432788040000000000000)
      constant := (1518549664363812456996844544617046910798687580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree086.table
  base := (75473311011550288140836416131104218459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-179480867759731436278380913740000000000000)
      constant := (4772248630967319167784919991395277605461475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225831795812724298497/50000000000000000000)
  centralHi := (90332718325089719399/20000000000000000000)
  directionLo := (454312667664021888871/100000000000000000000)
  directionHi := (56789083458002736109/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree087.table
  base := (102156576225077184630909513005441652723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-6475479238650615995687154301020000000000000)
      constant := (172634776315893927876065227200853335979921120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree087.table
  base := (817252405223546687289522189167828549543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-181504867659772049087729686080000000000000)
      constant := (4882743780843999189627679871883839142747715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454312667664021888871/100000000000000000000)
  centralHi := (56789083458002736109/12500000000000000000)
  directionLo := (456946386351834497139/100000000000000000000)
  directionHi := (22847319317591724857/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree088.table
  base := (158489921955336012389951081673125386053/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-58929017115768580672985344630320000000000000)
      constant := (1589279987387620009003055783169075705003246880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree088.table
  base := (316979801445958991376939719288945803847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-183528867559812661897078458420000000000000)
      constant := (4994507235412676049314213498673778916076940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456946386351834497139/100000000000000000000)
  centralHi := (22847319317591724857/5000000000000000000)
  directionLo := (114891252930760573197/25000000000000000000)
  directionHi := (459565011723042292789/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree089.table
  base := (1729367067699625274008798949861519679863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-59578721083681617384786300551460000000000000)
      constant := (1625250665946922167204658399322841161881378060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree089.table
  base := (345873385337044150088358979301128464797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-185552867459853274706427230760000000000000)
      constant := (5107538994523082754219935385524528211619925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114891252930760573197/25000000000000000000)
  centralHi := (459565011723042292789/100000000000000000000)
  directionLo := (115542200082913429003/25000000000000000000)
  directionHi := (462168800331653716013/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree090.table
  base := (1100797828429783252270555694173523353341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-2230682409318320522095824313800000000000000)
      constant := (61541667499029281786813831169950822802400920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree090.table
  base := (2201595539806151684241823718275281393449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-187576867359893887515776003100000000000000)
      constant := (5221839058034611557555596499791376406967245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115542200082913429003/25000000000000000000)
  centralHi := (462168800331653716013/100000000000000000000)
  directionLo := (464758001544890026221/100000000000000000000)
  directionHi := (232379000772445013111/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree091.table
  base := (2684605115844964332237094318937316503947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-60878129019507690808388212393740000000000000)
      constant := (1698403056924035705238264198293723952736394140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree091.table
  base := (21476840149544642320595403932522652067/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-189600867259934500325124775440000000000000)
      constant := (5337407425814994716937029742219826657541875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464758001544890026221/100000000000000000000)
  centralHi := (232379000772445013111/50000000000000000000)
  directionLo := (233666428910958452213/50000000000000000000)
  directionHi := (467332857821916904427/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree092.table
  base := (794598854741416618226703728484340620373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-61527832987420727520189168314880000000000000)
      constant := (1735584769256039411487142978257130527220017040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree092.table
  base := (3178395338341345962446750311497559430287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-191624867159975113134473547780000000000000)
      constant := (5454244097739208929336770863285487797151435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233666428910958452213/50000000000000000000)
  centralHi := (467332857821916904427/100000000000000000000)
  directionLo := (234946802489414611739/50000000000000000000)
  directionHi := (469893604978829223479/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree093.table
  base := (3682966541913416568268171102006175999993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-6908615217259307136887791581780000000000000)
      constant := (197018906603380261298910308458146611679998740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree093.table
  base := (3682966475012858135070699213252058542339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-193648867060015725943822320120000000000000)
      constant := (5572349073688563741923379368164260292711695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234946802489414611739/50000000000000000000)
  centralHi := (469893604978829223479/100000000000000000000)
  directionLo := (472440472440708661181/100000000000000000000)
  directionHi := (236220236220354330591/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree094.table
  base := (2099159230795247293990136687513034698429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-62827240923246800943791080157160000000000000)
      constant := (1811159227409766219398261350889140232422909960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree094.table
  base := (2099159203042028754706033275644920077963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-195672866960056338753171092460000000000000)
      constant := (5691722353549941358204184228628449200779630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472440472440708661181/100000000000000000000)
  centralHi := (236220236220354330591/50000000000000000000)
  directionLo := (237486841740758344693/50000000000000000000)
  directionHi := (474973683481516689387/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree095.table
  base := (4724451155966509427506765300871506590471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-63476944891159837655592036078300000000000000)
      constant := (1849551973158381781021999805134549340676563020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree095.table
  base := (472445110991880814386464240814979030629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-197696866860096951562519864800000000000000)
      constant := (5812363937215161098471154395090748951531450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237486841740758344693/50000000000000000000)
  centralHi := (474973683481516689387/100000000000000000000)
  directionLo := (238746727726266438979/50000000000000000000)
  directionHi := (477493455452532877959/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree096.table
  base := (2630682301979209661301546597547234175697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-7125183206563652707488110222160000000000000)
      constant := (209816488515790500989259106876749004303250920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree096.table
  base := (5261364565761830137593913597148542379981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-199720866760137564371868637140000000000000)
      constant := (5934273824580446563220117301617742711899905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238746727726266438979/50000000000000000000)
  centralHi := (477493455452532877959/100000000000000000000)
  directionLo := (24/5)
  directionHi := (480000000000000000001/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree097.table
  base := (232362351413189177025812500654224516191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-64776352826985911079193947920580000000000000)
      constant := (1927548497828181281389107031000745592905735500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree097.table
  base := (5809058753649068381797183677413639832667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-201744866660178177181217409480000000000000)
      constant := (6057452015545977476907059466005068199163335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24/5)
  centralHi := (480000000000000000001/100000000000000000000)
  directionLo := (241246761636296374141/50000000000000000000)
  directionHi := (482493523272592748283/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree098.table
  base := (3183766840302767010143263153164406452769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-65426056794898947790994903841720000000000000)
      constant := (1967152276685032751218843039392074676906971560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree098.table
  base := (3183766827166018689927766518087503757403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-203768866560218789990566181820000000000000)
      constant := (6181898510015511412048886290188875037574030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241246761636296374141/50000000000000000000)
  centralHi := (482493523272592748283/100000000000000000000)
  directionLo := (484974226119285642187/100000000000000000000)
  directionHi := (121243556529821410547/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree099.table
  base := (3468394635500330563322823140814054508683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-2447250398622666092696142954180000000000000)
      constant := (74339249377119886658708615705394186541041960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree099.table
  base := (6936789249213710864581506603843368601551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-205792866460259402799914954160000000000000)
      constant := (6307613307896063237309660498821216843007755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484974226119285642187/100000000000000000000)
  centralHi := (121243556529821410547/25000000000000000000)
  directionLo := (487442304278157621627/100000000000000000000)
  directionHi := (121860576069539405407/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree100.table
  base := (469801596147416403786559661323168642203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-66725464730725021214596815684000000000000000)
      constant := (2047570867290380400867672682026496531205901760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree100.table
  base := (7516825520293958700130714175794689894209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-207816866360300015609263726500000000000000)
      constant := (6434596409097632302010160140878973449471045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487442304278157621627/100000000000000000000)
  centralHi := (121860576069539405407/25000000000000000000)
  directionLo := (489897948556635619639/100000000000000000000)
  directionHi := (12247448713915890491/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree101.table
  base := (4053821232549895292261143448095764129403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-67375168698638057926397771605140000000000000)
      constant := (2088385678980983943617580107154435775779265720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree101.table
  base := (1621528490024577886535998148186933913069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-209840866260340628418612498840000000000000)
      constant := (6562847813532969148881269391306673347826725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489897948556635619639/100000000000000000000)
  centralHi := (12247448713915890491/2500000000000000000)
  directionLo := (492341345003646834697/100000000000000000000)
  directionHi := (246170672501823417349/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree102.table
  base := (4354620017088216505578187860959701084951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-7558319185172343848688747502920000000000000)
      constant := (236622685358492270645047427341303492390582360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree102.table
  base := (2177310005440187214304331227708724072501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-211864866160381241227961271180000000000000)
      constant := (6692367521117375006897928193162174481450020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492341345003646834697/100000000000000000000)
  centralHi := (246170672501823417349/50000000000000000000)
  directionLo := (247386337537059632989/50000000000000000000)
  directionHi := (494772675074119265979/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree103.table
  base := (9321618229034742639128374431108696600221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-68674576634464131349999683447420000000000000)
      constant := (2171226334999902645127011567242245588492358020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree103.table
  base := (9321618218743264585818043755785193374853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-213888866060421854037310043520000000000000)
      constant := (6823155531768528514120513181796925966874265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247386337537059632989/50000000000000000000)
  centralHi := (494772675074119265979/100000000000000000000)
  directionLo := (7768626809160033271/1562500000000000000)
  directionHi := (99438423157248425869/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree104.table
  base := (4972388516790712800097148243991506054881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-69324280602377168061800639368560000000000000)
      constant := (2213252179275329435515779012478020479617814440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree104.table
  base := (9944777025051523256128838097475297182921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-215912865960462466846658815860000000000000)
      constant := (6955211845406335103737257811319376485914605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7768626809160033271/1562500000000000000)
  centralHi := (99438423157248425869/20000000000000000000)
  directionLo := (499599839871871856467/100000000000000000000)
  directionHi := (124899959967967964117/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree105.table
  base := (1057871643215482991771768848330618360397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-7774887174476689419289066143300000000000000)
      constant := (250631300114148770085508680806232613048714600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree105.table
  base := (423148657003425137303824723609326005371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-217936865860503079656007588200000000000000)
      constant := (7088536461952795293570391632501165750671375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499599839871871856467/100000000000000000000)
  centralHi := (124899959967967964117/25000000000000000000)
  directionLo := (250998007960222664393/50000000000000000000)
  directionHi := (501996015920445328787/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree106.table
  base := (11223436409499628330939256314746580585901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-70623688538203241485402551210840000000000000)
      constant := (2298514900231217500725978855130687460549159620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree106.table
  base := (5611718201820759881108513883848049236113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-219960865760543692465356360540000000000000)
      constant := (7223129381331888781854907865510480492361130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250998007960222664393/50000000000000000000)
  centralHi := (501996015920445328787/100000000000000000000)
  directionLo := (504380808516739661249/100000000000000000000)
  directionHi := (403504646813391729/80000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree107.table
  base := (11878936950744511992660970793111800997673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-71273392506116278197203507131980000000000000)
      constant := (2341751776862873625052520388815310617616230260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree107.table
  base := (742433559118152671643816201471464600323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-221984865660584305274705132880000000000000)
      constant := (7358990603469471796097346470815717168025840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504380808516739661249/100000000000000000000)
  centralHi := (403504646813391729/80000000000000000)
  directionLo := (253377189186398545461/50000000000000000000)
  directionHi := (506754378372797090923/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree108.table
  base := (2509043608276482647246753933949071431181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-2663818387927011663296461594560000000000000)
      constant := (88347864107363179782564120276560721429354300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree108.table
  base := (12545218037360647840112328363755000468809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-224008865560624918084053905220000000000000)
      constant := (7496120128293185588574030527946775002344045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253377189186398545461/50000000000000000000)
  centralHi := (506754378372797090923/100000000000000000000)
  directionLo := (15909902576697319299/3125000000000000000)
  directionHi := (509116882454314217569/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree109.table
  base := (13222279667252859123267323297405779600939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-72572800441942351620805418974260000000000000)
      constant := (2429436562316074221795919097057642862953521180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree109.table
  base := (1652784957990121373398798363157640544143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-226032865460665530893402677560000000000000)
      constant := (7634517955732374339002657795488305621765720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15909902576697319299/3125000000000000000)
  centralHi := (509116882454314217569/100000000000000000000)
  directionLo := (255734237050888436571/50000000000000000000)
  directionHi := (511468474101776873143/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree110.table
  base := (13910121814526126224722420541962597066497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-73222504409855388332606374895400000000000000)
      constant := (2473884471092274576097540415549529407247725140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree110.table
  base := (278202436235320159994457461375824480287/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-228056865360706143702751449900000000000000)
      constant := (7774184085718011026444166464543956120071750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255734237050888436571/50000000000000000000)
  centralHi := (511468474101776873143/100000000000000000000)
  directionLo := (128452325786651290201/25000000000000000000)
  directionHi := (102761860629321032161/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree111.table
  base := (7304372234844461841700383258766932138747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-8208023153085380560489703424060000000000000)
      constant := (279859561911723931760603773914185595569948920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree111.table
  base := (2921748893480528952102122651778304812517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-230080865260746756512100222240000000000000)
      constant := (7915118518182630080312560667136457620312925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128452325786651290201/25000000000000000000)
  centralHi := (102761860629321032161/20000000000000000000)
  directionLo := (516139516022557606303/100000000000000000000)
  directionHi := (16129359875704925197/3125000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree112.table
  base := (7659073809765689107645833192944410734611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-74521912345681461756208286737680000000000000)
      constant := (2563991320634396656319502420454131890780139640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree112.table
  base := (1914768452204718246618024152765593133017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-232104865160787369321448994580000000000000)
      constant := (8057321253060265824124793331998623725320680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516139516022557606303/100000000000000000000)
  centralHi := (16129359875704925197/3125000000000000000)
  directionLo := (518459255872628818477/100000000000000000000)
  directionHi := (259229627936314409239/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree113.table
  base := (16038331251135133105882381370677833272367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-75171616313594498468009242658820000000000000)
      constant := (2609650261357990649642235144411227589901234540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree113.table
  base := (8019165624783419351820617593698197632519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-234128865060827982130797766920000000000000)
      constant := (8200792290286395893213952570274981976325190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518459255872628818477/100000000000000000000)
  centralHi := (259229627936314409239/50000000000000000000)
  directionLo := (13019216566291537037/2500000000000000000)
  directionHi := (520768662651661481481/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree114.table
  base := (8384647675931202452118391731787489026697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-8424591142389726131090022064440000000000000)
      constant := (295079208817313795180346178858385496049610920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree114.table
  base := (16769295350563654544376550981326726536709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-236152864960868594940146539260000000000000)
      constant := (8345531629797888945538912441098633632683545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13019216566291537037/2500000000000000000)
  centralHi := (520768662651661481481/100000000000000000000)
  directionLo := (130766968306220206567/25000000000000000000)
  directionHi := (523067873224880826269/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree115.table
  base := (17511039909345867611380775469214975857589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-76471024249420571891611154501100000000000000)
      constant := (2702179174607862109143805778940365760889294180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree115.table
  base := (875551995413520846451345170213984324943/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-238176864860909207749495311600000000000000)
      constant := (8491539271532956098269056758471398432494300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130766968306220206567/25000000000000000000)
  centralHi := (523067873224880826269/100000000000000000000)
  directionLo := (262678510731273942937/50000000000000000000)
  directionHi := (4202856171700383087/800000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree116.table
  base := (18263564911479255685735617588344839770541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-77120728217333608603412110422240000000000000)
      constant := (2749049147094492357026948093581126640428276420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree116.table
  base := (913178245529438942483325346026610166837/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-240200864760949820558844083940000000000000)
      constant := (8638815215431105616364756594714661016683700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262678510731273942937/50000000000000000000)
  centralHi := (4202856171700383087/800000000000000000)
  directionLo := (527636238330916766837/100000000000000000000)
  directionHi := (263818119165458383419/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree117.table
  base := (19026870346408594956997655510213520903857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-2880386377231357233896780234940000000000000)
      constant := (103567510992463387485801875320901311254231420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree117.table
  base := (951343517283566581959907968275283810929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-242224864660990433368192856280000000000000)
      constant := (8787359461433100456490525939005528381092900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527636238330916766837/100000000000000000000)
  centralHi := (263818119165458383419/50000000000000000000)
  directionLo := (105981130395934162257/20000000000000000000)
  directionHi := (264952825989835405643/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree118.table
  base := (9900478101261992608367786341518521121569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-78420136153159682027014022264520000000000000)
      constant := (2844000123695111386075254666376102008433883560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree118.table
  base := (19800956201913618212930230976424891225997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-244248864561031046177541628620000000000000)
      constant := (8937172009480918333222906642530124456129985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105981130395934162257/20000000000000000000)
  centralHi := (264952825989835405643/50000000000000000000)
  directionLo := (532165387826002829001/100000000000000000000)
  directionHi := (266082693913001414501/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree119.table
  base := (1286613904278241899148348998008226388837/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-79069840121072718738814978185660000000000000)
      constant := (2892081127771866968055467419791758727998655040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree119.table
  base := (823432898717863786795300874088373191561/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-246272864461071658986890400960000000000000)
      constant := (9088252859517714027056997705783046648945125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532165387826002829001/100000000000000000000)
  centralHi := (266082693913001414501/50000000000000000000)
  directionLo := (53441556863549549851/10000000000000000000)
  directionHi := (534415568635495498511/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree120.table
  base := (10690734566523871100524357285134664155051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-8857727120998417272290659345200000000000000)
      constant := (326729534334302678296467874971448479095818360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree120.table
  base := (21381469132629492841406466660488611850609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-248296864361112271796239173300000000000000)
      constant := (9240602011487783697149556302102443059253045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53441556863549549851/10000000000000000000)
  centralHi := (534415568635495498511/100000000000000000000)
  directionLo := (268328157299974763569/50000000000000000000)
  directionHi := (536656314599949527139/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree121.table
  base := (1386743511586826978811721838591466354529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-80369248056898792162416890027940000000000000)
      constant := (2989454167387988558133852098813316307909391680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree121.table
  base := (11093948092521521782077993525272347691321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-250320864261152884605587945640000000000000)
      constant := (9394219465336530997683852039734723476913210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268328157299974763569/50000000000000000000)
  centralHi := (536656314599949527139/100000000000000000000)
  directionLo := (538887743412299181603/100000000000000000000)
  directionHi := (134721935853074795401/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree122.table
  base := (11502551807384774697332459073820971753339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-81018952024811828874217845949080000000000000)
      constant := (3038746202892315329670520316016041948480818360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree122.table
  base := (2875637951810378301572674395245444530093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-252344864161193497414936717980000000000000)
      constant := (9549105221010434826532136479377817781203720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538887743412299181603/100000000000000000000)
  centralHi := (134721935853074795401/25000000000000000000)
  directionLo := (541109970338747315897/100000000000000000000)
  directionHi := (270554985169373657949/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree123.table
  base := (372392053292050653127919214662267621681/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-9074295110302762842890977985580000000000000)
      constant := (343160212833855393827016362321654823001765120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree123.table
  base := (595827285261352914282706462691185236497/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-254368864061234110224285490320000000000000)
      constant := (9705259278457018559617537458596237047299400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541109970338747315897/100000000000000000000)
  centralHi := (270554985169373657949/50000000000000000000)
  directionLo := (271661554144122498797/50000000000000000000)
  directionHi := (108664621657648999519/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree124.table
  base := (6167964890715058647186617001088959867669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-82318359960637902297819757791360000000000000)
      constant := (3138541305208461802103865891229624459942495120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree124.table
  base := (24671859562664003639232621904211993276239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-256392863961274723033634262660000000000000)
      constant := (9862681637624820644934535201473059966381195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271661554144122498797/50000000000000000000)
  centralHi := (108664621657648999519/20000000000000000000)
  directionLo := (54552726787943423571/10000000000000000000)
  directionHi := (545527267879434235711/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree125.table
  base := (25521408061180139315814218497251486551677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-82968063928550939009620713712500000000000000)
      constant := (3189044371987248953372538231613984908213716740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree125.table
  base := (25521408061017760582073073159078722401073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-258416863861315335842983035000000000000000)
      constant := (10021372298463366447311722647045393612005365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54552726787943423571/10000000000000000000)
  centralHi := (545527267879434235711/100000000000000000000)
  directionLo := (34232659844072882091/6250000000000000000)
  directionHi := (547722557505166113457/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree126.table
  base := (13190868447873400895543175500026960912203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-3096954366535702804497098875320000000000000)
      constant := (119998189475000565498550823670237235309464360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree126.table
  base := (26381736895612443909278749777293886114769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-260440863761355948652331807340000000000000)
      constant := (10181331260923141249296345482838469430573845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34232659844072882091/6250000000000000000)
  centralHi := (547722557505166113457/100000000000000000000)
  directionLo := (54990908339470080079/10000000000000000000)
  directionHi := (549909083394700800791/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree127.table
  base := (13626423028421537010822693220779920743691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-84267471864377012433222625554780000000000000)
      constant := (3291261536706018967620341597581536443209558840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree127.table
  base := (136264230283659542719241167291058261283/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-262464863661396561461680579680000000000000)
      constant := (10342558524955564325503396617349058261283000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54990908339470080079/10000000000000000000)
  centralHi := (549909083394700800791/100000000000000000000)
  directionLo := (22083477986947617577/4000000000000000000)
  directionHi := (276043474836845219713/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree128.table
  base := (28134735534933793658482021795745200761421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-84917175832290049145023581475920000000000000)
      constant := (3342975634614813087845551236167219225233502020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree128.table
  base := (28134735534841822861264263765270210167517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-264488863561437174271029352020000000000000)
      constant := (10505054090512964017810289748394351050837585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22083477986947617577/4000000000000000000)
  centralHi := (276043474836845219713/50000000000000000000)
  directionLo := (69282032302755091741/12500000000000000000)
  directionHi := (554256258422040733929/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree129.table
  base := (29027405320660956862066181641960285514169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-9507431088911453984091615266340000000000000)
      constant := (377232601059581962546273603630222351392550420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree129.table
  base := (29027405320584871063390823983677740919903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-266512863461477787080378124360000000000000)
      constant := (10668817957548553747226344792400388704599515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69282032302755091741/12500000000000000000)
  centralHi := (554256258422040733929/100000000000000000000)
  directionLo := (11128342194594844503/2000000000000000000)
  directionHi := (556417109729742225151/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree130.table
  base := (3741356925604884017733088614282069389089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-86216583768116122568625493318200000000000000)
      constant := (3447614861455412196618411472649045619282593440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree130.table
  base := (14965427702388065739922374097121205283139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-268536863361518399889726896700000000000000)
      constant := (10833850126016408905399645919771212052831390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11128342194594844503/2000000000000000000)
  centralHi := (556417109729742225151/100000000000000000000)
  directionLo := (111713920350151529359/20000000000000000000)
  directionHi := (139642400437689411699/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree131.table
  base := (30845085778450684110188693256110756072647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-86866287736029159280426449239340000000000000)
      constant := (3500539990357728411223342321320784924837688140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree131.table
  base := (6169017155679724119665351577129940914343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-270560863261559012699075669040000000000000)
      constant := (11000150595871444574768696737950248522858575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111713920350151529359/20000000000000000000)
  centralHi := (139642400437689411699/25000000000000000000)
  directionLo := (70089228844380931739/12500000000000000000)
  directionHi := (560713830755047453913/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree132.table
  base := (15885048216321028632908473100201634458967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-9723999078215799554691933906720000000000000)
      constant := (394874310692093695024364072596720588405228120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree132.table
  base := (15885048216299496826945292250842286413903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-272584863161599625508424441380000000000000)
      constant := (11167719367069394031508765904156422864139030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70089228844380931739/12500000000000000000)
  centralHi := (560713830755047453913/100000000000000000000)
  directionLo := (562849891178811546547/100000000000000000000)
  directionHi := (140712472794702886637/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree133.table
  base := (32705887358719010923198394064909012583477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-88165695671855232704028361081620000000000000)
      constant := (3607601279054672155895621729432942100385232740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree133.table
  base := (16352943679341696742897396798808397150897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-274608863061640238317773213720000000000000)
      constant := (11336556439566787989816146246166083971508970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562849891178811546547/100000000000000000000)
  centralHi := (140712472794702886637/25000000000000000000)
  directionLo := (564977875673021376763/100000000000000000000)
  directionHi := (141244468918255344191/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree134.table
  base := (33652458548142897258106191437451179840649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-88815399639768269415829317002760000000000000)
      constant := (3661737438821382503777130059940428911341851380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree134.table
  base := (16826229274056720062315432818759910815273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-276632862961680851127121986060000000000000)
      constant := (11506661813320934549843795166299599108152730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564977875673021376763/100000000000000000000)
  centralHi := (141244468918255344191/25000000000000000000)
  directionLo := (283548937575156504059/50000000000000000000)
  directionHi := (567097875150313008119/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree135.table
  base := (6921961998505343034938022949447676569899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-3313522355840048375097417515700000000000000)
      constant := (137639899093162494706982380841046802970969700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree135.table
  base := (8652452498125588555660688525132580848041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-278656862861721463936470758400000000000000)
      constant := (11678035488289899814852932431952651616960820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283548937575156504059/50000000000000000000)
  centralHi := (567097875150313008119/100000000000000000000)
  directionLo := (569209978830308279759/100000000000000000000)
  directionHi := (7115124735378853497/1250000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree136.table
  base := (35577941683631353331983114292615757308079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-90114807575594342839431228845040000000000000)
      constant := (3771220789123339355457437777219765526839087980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree136.table
  base := (17788970841805604001834961288701888907827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-280680862761762076745819530740000000000000)
      constant := (11850677464432489145962755361079018889078270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569209978830308279759/100000000000000000000)
  centralHi := (7115124735378853497/1250000000000000000)
  directionLo := (571314274283427999839/100000000000000000000)
  directionHi := (3570714214271424999/625000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree137.table
  base := (36556853613361956216611054737682319949237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-90764511543507379551232184766180000000000000)
      constant := (3826567979632124832952204444230774858317763940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree137.table
  base := (2284803350834081118755500522725395029763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-282704862661802689555168303080000000000000)
      constant := (12024587741708229025335142140156031602381040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571314274283427999839/100000000000000000000)
  centralHi := (3570714214271424999/625000000000000000)
  directionLo := (573410847473258043177/100000000000000000000)
  directionHi := (286705423736629021589/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree138.table
  base := (37546545773764407626407657879679416670671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-10157135056824490695892571187480000000000000)
      constant := (431368760780984235702812768116980295000720780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree138.table
  base := (18773272886875316737077737443445321125897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-284728862561843302364517075420000000000000)
      constant := (12199766320077349500781385086322453211258970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573410847473258043177/100000000000000000000)
  centralHi := (286705423736629021589/50000000000000000000)
  directionLo := (575499782797526344991/100000000000000000000)
  directionHi := (17984368212422698281/3125000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree139.table
  base := (19273509078510963174082031921144922890187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-92063919479333452974834096608460000000000000)
      constant := (3938473391300876035011370830686275050164205880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree139.table
  base := (7709403631402107519989214928220309404199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-286752862461883915173865847760000000000000)
      constant := (12376213199500767186671852962047507735104975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575499782797526344991/100000000000000000000)
  centralHi := (17984368212422698281/3125000000000000000)
  directionLo := (36098822695484128489/6250000000000000000)
  directionHi := (23103246525109842233/4000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree140.table
  base := (19779135377725884590600059641661664006223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-92713623447246489686635052529600000000000000)
      constant := (3995031612435732530025270348716783791380162520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree140.table
  base := (19779135377721176608762349752906927063379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-288776862361924527983214620100000000000000)
      constant := (12553928379940068797706870226729069270633790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36098822695484128489/6250000000000000000)
  centralHi := (23103246525109842233/4000000000000000000)
  directionLo := (144913767461894385737/25000000000000000000)
  directionHi := (579655069847577542949/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree141.table
  base := (5072537945187754598074535163369129350789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-10373703046128836266492889827860000000000000)
      constant := (450221501157910392159413756405901046265136160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree141.table
  base := (40580303561494252269820141029662284604751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-290800862261965140792563392440000000000000)
      constant := (12732911861357495193601080838110311423023755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144913767461894385737/25000000000000000000)
  centralHi := (579655069847577542949/100000000000000000000)
  directionLo := (72715197861244935211/12500000000000000000)
  directionHi := (581721582889959481689/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree142.table
  base := (41613116567748578116210180233482971284483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-94013031383072563110236964371880000000000000)
      constant := (4109359085245231908551460568614144413480862460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree142.table
  base := (8322623313548428540049011722071457911727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-292824862162005753601912164780000000000000)
      constant := (12913163643715925914071548093179786447793175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72715197861244935211/12500000000000000000)
  centralHi := (581721582889959481689/100000000000000000000)
  directionLo := (583780780773056967893/100000000000000000000)
  directionHi := (291890390386528483947/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree143.table
  base := (42656709766891989491361503072166854689679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-94662735350985599822037920293020000000000000)
      constant := (4167128336896022633406298524554879804597279980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree143.table
  base := (42656709766886669630057765855031458317217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-294848862062046366411260937120000000000000)
      constant := (13094683726978864184724563559973157291586085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583780780773056967893/100000000000000000000)
  centralHi := (291890390386528483947/50000000000000000000)
  directionLo := (292916370317536196251/50000000000000000000)
  directionHi := (585832740635072392503/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree144.table
  base := (21855541575877352261378936012624542981959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-3530090345144393945697736156080000000000000)
      constant := (156492639457849557275993482349738945157835080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree144.table
  base := (8742216630350061410509534041211958081989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-296872861962086979220609709460000000000000)
      constant := (13277472111110422375526574275702298952049725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292916370317536196251/50000000000000000000)
  centralHi := (585832740635072392503/100000000000000000000)
  directionLo := (587877538267962743567/100000000000000000000)
  directionHi := (36742346141747671473/6250000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree145.table
  base := (11194059178819542853639805150779652568149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-95962143286811673245639832135300000000000000)
      constant := (4283877870631543293778776157565189648641605520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree145.table
  base := (2798514794704658536219701289309256810461/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-298896861862127592029958481800000000000000)
      constant := (13461528796075307894536582485194740544836880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587877538267962743567/100000000000000000000)
  centralHi := (36742346141747671473/6250000000000000000)
  directionLo := (589915248150105033373/100000000000000000000)
  directionHi := (294957624075052516687/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree146.table
  base := (45852170450520114275526295534379526579747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-96611847254724709957440788056440000000000000)
      constant := (4342858152693591888443347336621932833059190140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree146.table
  base := (45852170450517109956841022555825394638093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-300920861762168204839307254140000000000000)
      constant := (13646853781838809500483991215611126973190465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589915248150105033373/100000000000000000000)
  centralHi := (294957624075052516687/50000000000000000000)
  directionLo := (591945943477949682283/100000000000000000000)
  directionHi := (147986485869487420571/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree147.table
  base := (9387776870130375058315362925127999069793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-10806839024737527407693527108620000000000000)
      constant := (489138012393002378309636029273320699162813700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree147.table
  base := (46938884350649392232426637201777240174163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-302944861662208817648656026480000000000000)
      constant := (13833447068366784018608308273026886200870815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591945943477949682283/100000000000000000000)
  centralHi := (147986485869487420571/25000000000000000000)
  directionLo := (37123106012293745031/6250000000000000000)
  directionHi := (593969696196699920497/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree148.table
  base := (24018189204477917379463323557932728343591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-97911255190550783381042699898720000000000000)
      constant := (4462029747150949298888776646246174039833234840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree148.table
  base := (48036378408953782613274619935541255906437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-304968861562249430458004798820000000000000)
      constant := (14021308655625643444944546434285706279532185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37123106012293745031/6250000000000000000)
  centralHi := (593969696196699920497/100000000000000000000)
  directionLo := (595986577030053588773/100000000000000000000)
  directionHi := (297993288515026794387/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree149.table
  base := (49144652618822906127175693919852594947279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-98560959158463820092843655819860000000000000)
      constant := (4522221059524668850537856324462766703814591980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree149.table
  base := (49144652618821210190550367174438294343831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-306992861462290043267353571160000000000000)
      constant := (14210438543582342424948532681474191471719155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595986577030053588773/100000000000000000000)
  centralHi := (297993288515026794387/50000000000000000000)
  directionLo := (29899832775452106197/5000000000000000000)
  directionHi := (597996655509042123941/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree150.table
  base := (1256592674343752583468012014390693636587/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-11023407014041872978293845749000000000000000)
      constant := (509201783183071691368960629942362994183426400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree150.table
  base := (50263706973748701843429383348435704318861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-309016861362330656076702343500000000000000)
      constant := (14400836732204366093016144536742178521594305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29899832775452106197/5000000000000000000)
  centralHi := (597996655509042123941/100000000000000000000)
  directionLo := (6/1)
  directionHi := (600000000000000000001/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree151.table
  base := (51393541467338177878062110569839817826033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-99860367094289893516445567662140000000000000)
      constant := (4643814714509511631642036468950046004878173460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree151.table
  base := (12848385366834254938881537568008714720883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-311040861262371268886051115840000000000000)
      constant := (14592503221459718260065454409162174294417660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6/1)
  centralHi := (600000000000000000001/100000000000000000000)
  directionLo := (120399335546339291249/20000000000000000000)
  directionHi := (300998338865848228123/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree152.table
  base := (13133539023322330765752791301363311893443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-100510071062202930228246523583280000000000000)
      constant := (4705217057100065631676881864579906261069510640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree152.table
  base := (52534156093288366092658595324997864231707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-313064861162411881695399888180000000000000)
      constant := (14785438011316909936925551935632989321158535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120399335546339291249/20000000000000000000)
  centralHi := (300998338865848228123/50000000000000000000)
  directionLo := (301993377410829987889/50000000000000000000)
  directionHi := (603986754821659975779/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree153.table
  base := (26842775422702471610213999743051820938357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-3746658334448739516298054796460000000000000)
      constant := (176556410237380203608692430795434718512602840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree153.table
  base := (10737110169080830499691968556468088412063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-315088861062452494504748660520000000000000)
      constant := (14979641101744948181814602737529702210301575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301993377410829987889/50000000000000000000)
  centralHi := (603986754821659975779/100000000000000000000)
  directionLo := (605970296301724677201/100000000000000000000)
  directionHi := (302985148150862338601/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree154.table
  base := (54847725717583485492764330522092043000219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-101809478998029003651848435425560000000000000)
      constant := (4829232772427226713286249551359227109660354780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree154.table
  base := (13711931429395708041397789108300569687851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-317112860962493107314097432860000000000000)
      constant := (15175112492713325260695913133798011393757020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605970296301724677201/100000000000000000000)
  centralHi := (302985148150862338601/50000000000000000000)
  directionLo := (303973683071413272633/50000000000000000000)
  directionHi := (607947366142826545267/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree155.table
  base := (14005170175954583029747462640953931369557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-102459182965942040363649391346700000000000000)
      constant := (4891846145144218558458674525673018975274729360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree155.table
  base := (14005170175954448083912992037415136941513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-319136860862533720123446205200000000000000)
      constant := (15371852184192008109777480283798302738830260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303973683071413272633/50000000000000000000)
  centralHi := (607947366142826545267/100000000000000000000)
  directionLo := (4764984588117783199/781250000000000000)
  directionHi := (609918027279076249473/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree156.table
  base := (28602207899097875562542309573898977937599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-11456542992650564119494483029760000000000000)
      constant := (550540354950073420794895361207475632057535640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree156.table
  base := (11440883159639061034168661555970166524617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-321160860762574332932794977540000000000000)
      constant := (15569860176151428089870309336771254163115425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4764984588117783199/781250000000000000)
  centralHi := (609918027279076249473/100000000000000000000)
  directionLo := (611882341631134179603/100000000000000000000)
  directionHi := (152970585407783544901/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree157.table
  base := (58398930994892903445665025174063634825579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-103758590901768113787251303188980000000000000)
      constant := (5018283920637120400086479276960052588417437980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree157.table
  base := (58398930994892535025472492919594394389901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-323184860662614945742143749880000000000000)
      constant := (15769136468562471022745936880695971971949505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611882341631134179603/100000000000000000000)
  centralHi := (152970585407783544901/25000000000000000000)
  directionLo := (613840370128912261003/100000000000000000000)
  directionHi := (153460092532228065251/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree158.table
  base := (2980211314408795228997039516225689985641/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-104408294869681150499052259110120000000000000)
      constant := (5082108323394308504364657353076014355534768400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree158.table
  base := (29802113144087800112947018714718651703707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-325208860562655558551492522220000000000000)
      constant := (15969681061396467500036135484875186517037070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613840370128912261003/100000000000000000000)
  centralHi := (153460092532228065251/25000000000000000000)
  directionLo := (615792172733626097037/100000000000000000000)
  directionHi := (307896086366813048519/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree159.table
  base := (2432812066895917558498395306069047071763/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-11673110981954909690094801670140000000000000)
      constant := (571815155868119695419173354162260211822933500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree159.table
  base := (60820301672397687543811518464295153923579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-327232860462696171360841294560000000000000)
      constant := (16171493954625183455599423035083475769617895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615792172733626097037/100000000000000000000)
  centralHi := (307896086366813048519/50000000000000000000)
  directionLo := (617737808459220018947/100000000000000000000)
  directionHi := (154434452114805004737/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree160.table
  base := (15511789285499356325582190057188171823993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-105707702805507223922654170952400000000000000)
      constant := (5210968158884416901618940242191379353419474640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree160.table
  base := (62047157141997217620325929563326132077613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-329256860362736784170190066900000000000000)
      constant := (16374575148220810992641304499016630660388065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617737808459220018947/100000000000000000000)
  centralHi := (154434452114805004737/25000000000000000000)
  directionLo := (154919333848296675407/25000000000000000000)
  directionHi := (619677335393186701629/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree161.table
  base := (63284792691496231214101602421218716792897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-106357406773420260634455126873540000000000000)
      constant := (5276003591599452858439375287841439821204493140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree161.table
  base := (63284792691496059666984934922828230818803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-331280860262777396979538839240000000000000)
      constant := (16578924642155959457219518197656141154094015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154919333848296675407/25000000000000000000)
  centralHi := (619677335393186701629/100000000000000000000)
  directionLo := (621610810716802125341/100000000000000000000)
  directionHi := (310805405358401062671/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree162.table
  base := (2581328332619917421183459491497410737687/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 600000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (949)
      square := (20239999000406128093487723400000000000000)
      linear := (-3963226323753085086898373436840000000000000)
      constant := (197831211146275663960792385587592116106530500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree162.table
  base := (32266604157748896917807032676126559661163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-333304860162818009788887611580000000000000)
      constant := (16784542436403646750093191785049265596611630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621610810716802125341/100000000000000000000)
  centralHi := (310805405358401062671/50000000000000000000)
  directionLo := (623538290724795825669/100000000000000000000)
  directionHi := (62353829072479582567/10000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree163.table
  base := (8224050501085767092830882987362170583577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-107656814709246334058057038715820000000000000)
      constant := (5407285486925774536685056722757843230763157920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree163.table
  base := (6579240400868601971110464456013889963001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-335328860062858622598236383920000000000000)
      constant := (16991428530937290869186781879738694498150050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623538290724795825669/100000000000000000000)
  centralHi := (62353829072479582567/10000000000000000000)
  directionLo := (625459830844475575103/100000000000000000000)
  directionHi := (9772809856944930861/1562500000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree164.table
  base := (3353118988291140304945706246225880696941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-108306518677159370769857994636960000000000000)
      constant := (5473531949519962081088284107643646534580888400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree164.table
  base := (67062379765822709440807471995917026505759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-337352859962899235407585156260000000000000)
      constant := (17199582925730701675237042478971585132528795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625459830844475575103/100000000000000000000)
  centralHi := (9772809856944930861/1562500000000000000)
  directionLo := (627375485654324877367/100000000000000000000)
  directionHi := (78421935706790609671/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree165.table
  base := (68343135581746683899341391688296817934569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-12106246960563600831295438950900000000000000)
      constant := (615575787635960479937624621563030927228222420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree165.table
  base := (34171567790873302035450933600160841013069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-339376859862939848216933928600000000000000)
      constant := (17409005620758072873474870180451608410130690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627375485654324877367/100000000000000000000)
  centralHi := (78421935706790609671/12500000000000000000)
  directionLo := (314642654451045464097/50000000000000000000)
  directionHi := (125857061780418185639/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree166.table
  base := (17408667862842929410233332921501842335977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-109605926612985444193459906479240000000000000)
      constant := (5607235904528581846681216419371889938337130960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree166.table
  base := (17408667862842912928563859543277077588429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-341400859762980461026282700940000000000000)
      constant := (17619696615993974204464603024177541551768580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314642654451045464097/50000000000000000000)
  centralHi := (125857061780418185639/20000000000000000000)
  directionLo := (631189353522380001811/100000000000000000000)
  directionHi := (157797338380595000453/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree167.table
  base := (35468493684842770334941467307678830376273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-110255630580898480905260862400380000000000000)
      constant := (5674693396926654628836901226867768910419124520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree167.table
  base := (35468493684842743112997498190431543157109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-343424859663021073835631473280000000000000)
      constant := (17831655911413343837481875067482315431571090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631189353522380001811/100000000000000000000)
  centralHi := (157797338380595000453/25000000000000000000)
  directionLo := (633087671653776559307/100000000000000000000)
  directionHi := (158271917913444139827/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree168.table
  base := (72250083331747990071941127000557241750421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1800000000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (2847)
      square := (60719997001218384280463170200000000000000)
      linear := (-12322814949867946401895757591280000000000000)
      constant := (638061618434428844664954724169348303515075780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree168.table
  base := (72250083331747945112423103784802938026457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-345448859563061686644980245620000000000000)
      constant := (18044883506991480960058199120172014690132285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell228.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633087671653776559307/100000000000000000000)
  centralHi := (158271917913444139827/25000000000000000000)
  directionLo := (15874507866387543543/2500000000000000000)
  directionHi := (634980314655501741721/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 107
  qDenominator := 180
  table := BinomialMassData.Q107_180.Degree169.table
  base := (73573959332689662572226154510773196471199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16200000000000000000000000000000000000000000
      center := (37557)
      previous := (0)
      next := (25623)
      square := (546479973010965458524168531800000000000000)
      linear := (-111555038516724554328862774242660000000000000)
      constant := (5810819411470308332818981849325038078283342380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_180.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree169.table
  base := (7357395933268962544616096291603784229509/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (78)
      square := (1686666583367177341123976950000000000000)
      linear := (-347472859463102299454329017960000000000000)
      constant := (18259379402704038557556681194902189211475450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell228.Kernel169
