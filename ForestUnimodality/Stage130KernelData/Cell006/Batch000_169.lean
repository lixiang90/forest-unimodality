import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell006.Parameters
import ForestUnimodality.BinomialMassData.Q37_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_126.Batch100_149
import ForestUnimodality.BinomialMassData.Q37_126.Batch150_199
import ForestUnimodality.BinomialMassData.Q19_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q19_63.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree000.table
  base := (329785632970087990766927531/50000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (15284894135232576957428296530000000000000)
      constant := (4155298975423108683663286890600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree000.table
  base := (329785632970087990766927531/50000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (7642447067616288478714148265000000000000)
      constant := (2077649487711554341831643445300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree001.table
  base := (47598086197629949827205679907364419249181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (614318404178122110873006010830000000000000)
      constant := (188685221304171772233266380926884379999999389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree001.table
  base := (9421233667168852926307541966925264802217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (604895973736459131482601235950000000000000)
      constant := (186727961158451075861333399742921879999996365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (7248455080507928537/25000000000000000000)
  directionHi := (28993820322031714149/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree002.table
  base := (6879739809065671373618939484887411643361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (265688477836591873428029340270000000000000)
      constant := (136167646337025859233240850547420684062499045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree002.table
  base := (16848930366572764019100142060398978371441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (123421808476632957323609895255000000000000)
      constant := (66690975680467098431520060290373545156249329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/25000000000000000000)
  centralHi := (28993820322031714149/100000000000000000000)
  directionLo := (820069078488518167/2000000000000000000)
  directionHi := (41003453924425908351/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree003.table
  base := (24864812036787757896405449516977433088401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-9215716500548707112994147810000000000000)
      constant := (10922312988336437717210122935412047991984841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree003.table
  base := (4822706232722659223128387884601410147799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-12356526647769700243129072770000000000000)
      constant := (10591254935684932433885749784216109375896795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/2000000000000000000)
  centralHi := (41003453924425908351/100000000000000000000)
  directionLo := (50218769903281956403/100000000000000000000)
  directionHi := (12554692475820489101/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree004.table
  base := (8968978949595641801030328988039358215181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-431571374846468601461924000850000000000000)
      constant := (70883676372367858606520431329596425512106778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree004.table
  base := (1721929194532368718525662198927787209313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-234630548306560259511771550185000000000000)
      constant := (34022795064792887302370427416461937168816485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50218769903281956403/100000000000000000000)
  centralHi := (12554692475820489101/25000000000000000000)
  directionLo := (7248455080507928537/12500000000000000000)
  directionHi := (57987640644063428297/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree005.table
  base := (12867918141915155901320445700422113959913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-780201301187998838906900671410000000000000)
      constant := (50938607579759841473765253064950370306894697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree005.table
  base := (12220392435779448874064093774947164637211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-827313453396313735858924545810000000000000)
      constant := (48400473186126750293988876106415296445090459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/12500000000000000000)
  centralHi := (57987640644063428297/100000000000000000000)
  directionLo := (64832153167477756241/100000000000000000000)
  directionHi := (32416076583738878121/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree006.table
  base := (9161316301003079339413684630301016266303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-125425691947725452927986371330000000000000)
      constant := (4056377703529039044070996039532748173439623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree006.table
  base := (1074761824372589364258625152204599080547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-65853656121083719594128110625000000000000)
      constant := (1907059572779324986391236310518912778084908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64832153167477756241/100000000000000000000)
  centralHi := (32416076583738878121/50000000000000000000)
  directionLo := (71020065482915145463/100000000000000000000)
  directionHi := (8877508185364393183/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree007.table
  base := (641000632306389513138267009073998621867/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-211065879124437044828122001790000000000000)
      constant := (3710017134637554165377776478164572185985890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree007.table
  base := (5930584672511316817969252963646109767591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-220488309566100024218526776670000000000000)
      constant := (3450172675126757180256998099837344238224097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71020065482915145463/100000000000000000000)
  centralHi := (8877508185364393183/12500000000000000000)
  directionLo := (38355219064893288933/50000000000000000000)
  directionHi := (76710438129786577867/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree008.table
  base := (4343610006966458466026179216057515115117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-1826091080212589551241830683090000000000000)
      constant := (18253638331574911001124012485132277491899373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree008.table
  base := (394078819566314644744912706080147139027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-950735261872946693182534441065000000000000)
      constant := (8386586925763310306641987503400519973990815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/50000000000000000000)
  centralHi := (76710438129786577867/100000000000000000000)
  directionLo := (820069078488518167/1000000000000000000)
  directionHi := (82006907848851816701/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree009.table
  base := (554300025389860074886303739031215190069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-241635667394902198742978594850000000000000)
      constant := (1400150560005575176607024001998829494102145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree009.table
  base := (1217703732682380873886152260664804347141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-125529048918282589066691684865000000000000)
      constant := (634764951073958738569376025038178717089181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/1000000000000000000)
  centralHi := (82006907848851816701/100000000000000000000)
  directionLo := (21745365241523785611/25000000000000000000)
  directionHi := (17396292193219028489/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree010.table
  base := (1557775108366313685859048714574270026627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-2523350932895650026131784024210000000000000)
      constant := (8473876718118276561996415526095277735682563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree010.table
  base := (639043932733137005770501475242251866039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-1308787618656139910017915886505000000000000)
      constant := (3783901528901151012515784352886497656308791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21745365241523785611/25000000000000000000)
  centralHi := (17396292193219028489/20000000000000000000)
  directionLo := (91686510287296855559/100000000000000000000)
  directionHi := (2292162757182421389/2500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree011.table
  base := (75672062452172768130723634323418696153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-2871980859237180263576760694770000000000000)
      constant := (5485978371378349501584842596742190440250056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree011.table
  base := (93111997966023217298181638049173945927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-1487813797047736518435606609225000000000000)
      constant := (2408368937026302314419414978729342782768526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91686510287296855559/100000000000000000000)
  centralHi := (2292162757182421389/2500000000000000000)
  directionLo := (96161623247160565677/100000000000000000000)
  directionHi := (48080811623580282839/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree012.table
  base := (-31034600982561648579321265659188016807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-357845642842078944557970818370000000000000)
      constant := (373544952649246018057405727241490422940565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree012.table
  base := (-349817834037048716371877240451961887289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-370408883430962917078510518210000000000000)
      constant := (322385369970838915047024651960684807705551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96161623247160565677/100000000000000000000)
  centralHi := (48080811623580282839/50000000000000000000)
  directionLo := (100437539806563912807/100000000000000000000)
  directionHi := (12554692475820489101/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree013.table
  base := (-193437618265118936916374362703232421557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-3569240711920240738466714035890000000000000)
      constant := (1903693243270920232363020703098482075361068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree013.table
  base := (-234319238044554910566479462243049531451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-1845866153830929735270988054665000000000000)
      constant := (814615326315518196071406571179672819341962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100437539806563912807/100000000000000000000)
  centralHi := (12554692475820489101/12500000000000000000)
  directionLo := (26134676460668794933/25000000000000000000)
  directionHi := (104538705842675179733/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree014.table
  base := (-160786044587331576298129603206827981649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-559695805465967282273098672350000000000000)
      constant := (138389782596771820871741238323828275240136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree014.table
  base := (-284920275735207994101234433821295156249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-578540666349293241053908222110000000000000)
      constant := (123201658680885438979002326056628232034085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26134676460668794933/25000000000000000000)
  centralHi := (104538705842675179733/100000000000000000000)
  directionLo := (108484941978726379241/100000000000000000000)
  directionHi := (54242470989363189621/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree015.table
  base := (-859391725583689366949656133880922471223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-474055618289255690372963041890000000000000)
      constant := (50425444206449258816218989242026380381314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree015.table
  base := (-1836664270612698327570130533757444533157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-489759669025360656023637666690000000000000)
      constant := (55809960409314291007185795162966960877763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108484941978726379241/100000000000000000000)
  centralHi := (54242470989363189621/50000000000000000000)
  directionLo := (112292583250158993679/100000000000000000000)
  directionHi := (1403657290626987421/1250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree016.table
  base := (-1045070032718982813062616905245993628293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-4615130490944831450801644047570000000000000)
      constant := (283963600005706607172151485437302578610166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree016.table
  base := (-1095706840985732054984501561582933540537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-2382944689005719560524060222825000000000000)
      constant := (238814462562165898012393779597336777608647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112292583250158993679/100000000000000000000)
  centralHi := (1403657290626987421/1250000000000000000)
  directionLo := (7248455080507928537/6250000000000000000)
  directionHi := (115975281288126856593/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree017.table
  base := (-2414187847240024206860118682269415495059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-4963760417286361688246620718130000000000000)
      constant := (404242412781566838905178335427689900110829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree017.table
  base := (-500378055705000612369686281227765273819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-5123941734794632337883501891090000000000000)
      constant := (736671052635997265219311500884998141061945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/6250000000000000000)
  centralHi := (115975281288126856593/100000000000000000000)
  directionLo := (119544583677916611033/100000000000000000000)
  directionHi := (59772291838958305517/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree018.table
  base := (-2701115190559711503961269684462698437553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-590265593736432436187955265410000000000000)
      constant := (86025300050507420108824070501949989039127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree018.table
  base := (-2777645580893886823501301618151183792609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-609110454619758394968764815170000000000000)
      constant := (137945115652864020702864279215327947459431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119544583677916611033/100000000000000000000)
  centralHi := (59772291838958305517/50000000000000000000)
  directionLo := (2460207235465554501/2000000000000000000)
  directionHi := (123010361773277725051/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree019.table
  base := (-2958488698979732276448631181896437909341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-5661020269969422163136574059250000000000000)
      constant := (1363887613404951244844707198718037937825571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree019.table
  base := (-302574024683617098696502028941584391103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-2920023224180509385777132390985000000000000)
      constant := (982055069600972957273861038469257758560965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2460207235465554501/2000000000000000000)
  centralHi := (123010361773277725051/100000000000000000000)
  directionLo := (63190566385456075119/50000000000000000000)
  directionHi := (126381132770912150239/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree020.table
  base := (-398997415621647658645529687140192335581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-6009650196310952400581550729810000000000000)
      constant := (2150714141267007188223015801824612960632088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree020.table
  base := (-1625723996706627824922335678077939376463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-3099049402572105994194823113705000000000000)
      constant := (1441775982298904731245282025008658614818353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63190566385456075119/50000000000000000000)
  centralHi := (126381132770912150239/100000000000000000000)
  directionLo := (64832153167477756241/50000000000000000000)
  directionHi := (129664306334955512483/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree021.table
  base := (-3405880538115743676712279066304387363651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-100925081311944168857563926990000000000000)
      constant := (49486769893568890059211279407823596089987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree021.table
  base := (-1729376525661428049839637053677732976281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (-52032945729582580993849425975000000000000)
      constant := (31619191312889959158031245033302822494297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64832153167477756241/50000000000000000000)
  centralHi := (129664306334955512483/100000000000000000000)
  directionLo := (132866376311659239359/100000000000000000000)
  directionHi := (415207425973935123/312500000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree022.table
  base := (-3603478929656492313382613100747105792993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-6706910048994012875471504070930000000000000)
      constant := (4251700218820879901450148329664737107610783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree022.table
  base := (-228168916888684537655081528955584916827/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-3457101759355299211030204559145000000000000)
      constant := (2626707013902137206504161810952267720909096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132866376311659239359/100000000000000000000)
  centralHi := (415207425973935123/312500000000000000)
  directionLo := (13599307177594637549/10000000000000000000)
  directionHi := (135993071775946375491/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree023.table
  base := (-3787320016798184426217407079071128897251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-7055539975335543112916480741490000000000000)
      constant := (5542712130067383157872166260091689406810781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree023.table
  base := (-1914828874013895276591343397051251663351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-3636127937746895819447895281865000000000000)
      constant := (3341184663934480083647458234018582148159881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599307177594637549/10000000000000000000)
  centralHi := (135993071775946375491/100000000000000000000)
  directionLo := (139049477481664640317/100000000000000000000)
  directionHi := (69524738740832320159/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree024.table
  base := (-1979699764967413790905686477922229755047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-822685544630785927817939712450000000000000)
      constant := (775864575900059312353550294032593356048546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree024.table
  base := (-3997471755264854068115907722455839647129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-847812025808553872859019112130000000000000)
      constant := (918169731238026184338675111916974715616111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139049477481664640317/100000000000000000000)
  centralHi := (69524738740832320159/50000000000000000000)
  directionLo := (142040130965830290927/100000000000000000000)
  directionHi := (8877508185364393183/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree025.table
  base := (-51516270473320536005054608051191854819/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-7752799828018603587806434082610000000000000)
      constant := (8565619811956223314527511431460562257871120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree025.table
  base := (-4155619099851593925153127308630687717503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-7988360589060178072566553454610000000000000)
      constant := (9991036862583862750893198960294800449230593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142040130965830290927/100000000000000000000)
  centralHi := (8877508185364393183/6250000000000000000)
  directionLo := (7248455080507928537/5000000000000000000)
  directionHi := (144969101610158570741/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree026.table
  base := (-4274299320187223277874848119584605261187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-8101429754360133825251410753170000000000000)
      constant := (10286175560615574226027258785798701718348797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree026.table
  base := (-430528776300782554228528084750379205727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-4173206472921685644700967450025000000000000)
      constant := (5930091037366197024412131570898724662347685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/5000000000000000000)
  centralHi := (144969101610158570741/100000000000000000000)
  directionLo := (147840055595642751097/100000000000000000000)
  directionHi := (73920027797821375549/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree027.table
  base := (-4419427676382106942587534686113859122739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-938895520077962673632931935970000000000000)
      constant := (1348926679914710283937956435168788126872101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree027.table
  base := (-4447446617252816649257293586075125524803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-967162811402951611804146260610000000000000)
      constant := (1540790862506539548164851138490869643561877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147840055595642751097/100000000000000000000)
  centralHi := (73920027797821375549/50000000000000000000)
  directionLo := (15065630970984586921/10000000000000000000)
  directionHi := (150656309709845869211/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree028.table
  base := (-1139384458204236609733725641564620019953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-1256955658149027757163052013470000000000000)
      constant := (2017819338179633467813832662031441794746596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree028.table
  base := (-916578948687372482243691878104994249333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-1294645379915679674724671112990000000000000)
      constant := (2286953196309775270627691845612341303140945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15065630970984586921/10000000000000000000)
  centralHi := (150656309709845869211/100000000000000000000)
  directionLo := (38355219064893288933/25000000000000000000)
  directionHi := (153420876259573155733/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree029.table
  base := (-4689336893838864425397882803395611493703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-9147319533384724537586340764850000000000000)
      constant := (16236554807536969552282105627737817981492793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree029.table
  base := (-471229789657973927611864928642670720031/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-4710285008096475469954039618185000000000000)
      constant := (9141101763943807104820886529951199560984805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/25000000000000000000)
  centralHi := (153420876259573155733/100000000000000000000)
  directionLo := (78068250411293189741/50000000000000000000)
  directionHi := (156136500822586379483/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree030.table
  base := (-4815417814087534288881015816073283458081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1055105495525139419447924159490000000000000)
      constant := (2052605000345126079508146441761681994986279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree030.table
  base := (-4836215751535627638112855109934339660313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1086513596997349350749273409090000000000000)
      constant := (2298387763802241766091809785618956209801967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78068250411293189741/50000000000000000000)
  centralHi := (156136500822586379483/100000000000000000000)
  directionLo := (79402847093142347173/50000000000000000000)
  directionHi := (158805694186284694347/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree031.table
  base := (-246814097850736963857918520387212664709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-9844579386067785012476294105970000000000000)
      constant := (20833416042424802054155186597668058675399580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree031.table
  base := (-4955122494371117014312458049042982448303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-10136674729759337373578842127250000000000000)
      constant := (23216649368667818156532316016138402662685393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79402847093142347173/50000000000000000000)
  centralHi := (158805694186284694347/100000000000000000000)
  directionLo := (8071537976565252397/5000000000000000000)
  directionHi := (161430759531305047941/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree032.table
  base := (-505235631578477521127821675434181660851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-10193209312409315249921270776530000000000000)
      constant := (23314773189623881454287127164897329880823810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree032.table
  base := (-5069422577658746742653020926765788220441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-10494727086542530590414223572690000000000000)
      constant := (25874076738970132362493608052066586553069671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8071537976565252397/5000000000000000000)
  centralHi := (161430759531305047941/100000000000000000000)
  directionLo := (820069078488518167/500000000000000000)
  directionHi := (164013815697703633401/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree033.table
  base := (-2582003406362485765988706520798741069223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1171315470972316165262916383010000000000000)
      constant := (2879562677665133596187172170930510376945314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree033.table
  base := (-1294865733108769435523810358238902053231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-602932191295873544847200278785000000000000)
      constant := (1592021945324611568075286391518288389050258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (820069078488518167/500000000000000000)
  centralHi := (164013815697703633401/100000000000000000000)
  directionLo := (166556817202378582213/100000000000000000000)
  directionHi := (83278408601189291107/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree034.table
  base := (-1054309739097209376578632969210540955711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-10890469165092375724811224117650000000000000)
      constant := (28636037552586062491751384784806814733915205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree034.table
  base := (-660692819970266355643177836165163400837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-5605415900054458512042493231785000000000000)
      constant := (15781208732035642530449719955931865848311788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166556817202378582213/100000000000000000000)
  centralHi := (83278408601189291107/50000000000000000000)
  directionLo := (16906157154555500351/10000000000000000000)
  directionHi := (169061571545555003511/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree035.table
  base := (-1075050952960158135389477791032856887761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-1605585584490557994608028684030000000000000)
      constant := (4496230114902145807514363596396850723197565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree035.table
  base := (-5387920164091259752466351343335029871063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-1652697736698872891560052558430000000000000)
      constant := (4941588183669648575885123205979038063107279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16906157154555500351/10000000000000000000)
  centralHi := (169061571545555003511/100000000000000000000)
  directionLo := (34305950848398924639/20000000000000000000)
  directionHi := (42882438560498655799/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree036.table
  base := (-5475361966771078074777964760450654067773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1287525446419492911077908606530000000000000)
      constant := (3825315935010526037295587489261261556112107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree036.table
  base := (-1097364061275609942479415545111732599739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1325215168186144828639527706050000000000000)
      constant := (4193511466473228365065192430588629617575505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34305950848398924639/20000000000000000000)
  centralHi := (42882438560498655799/25000000000000000000)
  directionLo := (21745365241523785611/12500000000000000000)
  directionHi := (173962921932190284889/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree037.table
  base := (-1114415347663973244676569976034300805927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-11936358944116966437146154129330000000000000)
      constant := (37497916036777986624495717683654300506378685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree037.table
  base := (-697804803042070804279756516795548695931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-6142494435229248337295565399945000000000000)
      constant := (20506549754749352011929280488978868903399444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21745365241523785611/12500000000000000000)
  centralHi := (173962921932190284889/100000000000000000000)
  directionLo := (17636252386505357237/10000000000000000000)
  directionHi := (176362523865053572371/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree038.table
  base := (-1416394847770549594745206009034584752933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-12284988870458496674591130799890000000000000)
      constant := (40683113012485290835174499299816932462435692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree038.table
  base := (-5674944974391596537815236132715835080593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-12643041227241689891426512245330000000000000)
      constant := (44404929677856508151922108306430850565126383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17636252386505357237/10000000000000000000)
  centralHi := (176362523865053572371/100000000000000000000)
  directionLo := (44682477998174694219/25000000000000000000)
  directionHi := (178729911992698776877/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree039.table
  base := (-2878013872365584031595172849404755473849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1403735421866669656892900830050000000000000)
      constant := (4886978661770459864488107842510005672065182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree039.table
  base := (-5764488883611418689604595936616478119299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1444565953780542567584654854530000000000000)
      constant := (5324055845755385515837140438822133149389141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44682477998174694219/25000000000000000000)
  centralHi := (178729911992698776877/100000000000000000000)
  directionLo := (181066349877010856143/100000000000000000000)
  directionHi := (11316646867313178509/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree040.table
  base := (-5843560167151802189249510440263217373039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-12982248723141557149481084141010000000000000)
      constant := (47396451684988858641509130206395290246408209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree040.table
  base := (-1462800113087251475225196957362035781157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-6679572970404038162548637568105000000000000)
      constant := (25773650574611819306933268559060159969175734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181066349877010856143/100000000000000000000)
  centralHi := (11316646867313178509/6250000000000000000)
  directionLo := (183373020574593711119/100000000000000000000)
  directionHi := (2292162757182421389/1250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree041.table
  base := (-5928298140043266170677920832130819350537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-13330878649483087386926060811570000000000000)
      constant := (50923562038785462892263675564427777997718647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree041.table
  base := (-5935193813994117319483331687057555334553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-13717198297591269541932656581650000000000000)
      constant := (55296872294708061008382013425358562877159143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183373020574593711119/100000000000000000000)
  centralHi := (2292162757182421389/1250000000000000000)
  directionLo := (92825516819887175493/50000000000000000000)
  directionHi := (185651033639774350987/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree042.table
  base := (-1202069688046502289605273889412059158203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-217135056759120914672556150510000000000000)
      constant := (866090717779329861350960491045201365166055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree042.table
  base := (-752071129160934375979902435135170537633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (-111708338526781450466413000215000000000000)
      constant := (469562054692823896508490648695937024516484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92825516819887175493/50000000000000000000)
  centralHi := (185651033639774350987/100000000000000000000)
  directionLo := (93950715681657911089/50000000000000000000)
  directionHi := (187901431363315822179/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree043.table
  base := (-6089805006229070628438233526079832885963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-14028138502166147861816014152690000000000000)
      constant := (58316538386981478842297572051014143275612853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree043.table
  base := (-609541390636215100539528328903068446733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-7216651505578827987801709736265000000000000)
      constant := (31575396238067362772222432766733606674583615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93950715681657911089/50000000000000000000)
  centralHi := (187901431363315822179/100000000000000000000)
  directionLo := (38025038869276200191/20000000000000000000)
  directionHi := (47531298586595250239/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree044.table
  base := (-770843818026994010508006504565811182539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-14376768428507678099260990823250000000000000)
      constant := (62181703278596195394759369748566363332021672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree044.table
  base := (-1234361102429996342970327456717300405423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-14791355367940849192438800917970000000000000)
      constant := (67254487122944346079190391667325173454380565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38025038869276200191/20000000000000000000)
  centralHi := (47531298586595250239/25000000000000000000)
  directionLo := (96161623247160565677/50000000000000000000)
  directionHi := (38464649298864226271/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree045.table
  base := (-780157239530457503252552179809819895439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1636155372761023148522885277090000000000000)
      constant := (7350991189495942189841572061605955408891208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree045.table
  base := (-97590805541846864681812857469851500123/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-841633762484669022737454575745000000000000)
      constant := (3970868561913365997161205248210455630264224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96161623247160565677/50000000000000000000)
  centralHi := (38464649298864226271/20000000000000000000)
  directionLo := (194496459502433268723/100000000000000000000)
  directionHi := (48624114875608317181/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree046.table
  base := (-6313391344796001783091944659390722640817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-15074028281190738574150944164370000000000000)
      constant := (70247935768545100495795771821608221838597327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree046.table
  base := (-6317491528133770368393391025978026585881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-15507460081507235626109563808850000000000000)
      constant := (75813997318195381160146963600433212480638311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194496459502433268723/100000000000000000000)
  centralHi := (48624114875608317181/25000000000000000000)
  directionLo := (196645656895462412259/100000000000000000000)
  directionHi := (9832282844773120613/5000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree047.table
  base := (-6383207461358368776396024132766999732261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-15422658207532268811595920834930000000000000)
      constant := (74448523697475539206009316919452778062656091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree047.table
  base := (-3193448865358585407564672873798651163977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-7932756219145214421472472627145000000000000)
      constant := (40134684581325518206668978354368153530175287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196645656895462412259/100000000000000000000)
  centralHi := (9832282844773120613/5000000000000000000)
  directionLo := (6211613052310562617/3125000000000000000)
  directionHi := (39754323534787600749/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree048.table
  base := (-322537811079551444172446963273657002331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1752365348208199894337877500610000000000000)
      constant := (8751165135359910292594739445126345239440580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree048.table
  base := (-806759518595624784787405963115503012479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-901309155281867892210018149985000000000000)
      constant := (4713420396002088768900297073624252685987044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6211613052310562617/3125000000000000000)
  centralHi := (39754323534787600749/20000000000000000000)
  directionLo := (100437539806563912807/50000000000000000000)
  directionHi := (40175015922625565123/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree049.table
  base := (-1629020426449090252374012717494573675929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-2302845437173618469497982025150000000000000)
      constant := (11883378339445131271843849859567306902993028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree049.table
  base := (-6519067229050271453580189771688549653659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-2368802450265259325230815449310000000000000)
      constant := (12790061525873279176800964833442592346375347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100437539806563912807/50000000000000000000)
  centralHi := (40175015922625565123/20000000000000000000)
  directionLo := (50739185563555499759/25000000000000000000)
  directionHi := (202956742254221999037/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree050.table
  base := (-6579222820285050104753413591712239534347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-16468547986556859523930850846610000000000000)
      constant := (87717855751958609447264678064244121288176757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree050.table
  base := (-822738319290666716689533568182027923569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-8469834754320004246725544795305000000000000)
      constant := (47167909296966527340267328419792124685418556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50739185563555499759/25000000000000000000)
  centralHi := (202956742254221999037/100000000000000000000)
  directionLo := (205017269622129541751/100000000000000000000)
  directionHi := (25627158702766192719/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree051.table
  base := (-3320106956392933138474983049674672266621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1868575323655376640152869724130000000000000)
      constant := (10262552446625752856538853841331939060840278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree051.table
  base := (-6642625434877971327082700755519727048769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1921969096158133523365163448450000000000000)
      constant := (11028622955107297300618491238125800371492871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205017269622129541751/100000000000000000000)
  centralHi := (25627158702766192719/12500000000000000000)
  directionLo := (103528646349910346719/50000000000000000000)
  directionHi := (207057292699820693439/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree052.table
  base := (-3349542656528376331843996943550975587027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-17165807839239919998820804187730000000000000)
      constant := (97118876800326141374518497413672355790179674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree052.table
  base := (-6701251426997999690094054048094642220237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-17655774222206394927121852481490000000000000)
      constant := (104295685316296539768574027756912365027879347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103528646349910346719/50000000000000000000)
  centralHi := (207057292699820693439/100000000000000000000)
  directionLo := (41815482337070071893/20000000000000000000)
  directionHi := (104538705842675179733/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree053.table
  base := (-3377931904115850078334831146816677290751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-17514437765581450236265780858290000000000000)
      constant := (101985463775906896595105222360144215666018562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree053.table
  base := (-1689452196926208977224960252506606577851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-9006913289494794071978616963465000000000000)
      constant := (54724979239407790226918130611867556985018762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41815482337070071893/20000000000000000000)
  centralHi := (104538705842675179733/50000000000000000000)
  directionLo := (211078198054445543089/100000000000000000000)
  directionHi := (21107819805444554309/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree054.table
  base := (-425660816318580267512516748658078255939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-1984785299102553385967861947650000000000000)
      constant := (11884737669863791457182459663278599826094416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree054.table
  base := (-6812318873796655502378641392838628654997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2041319881752531262310290596930000000000000)
      constant := (12746704590932315458547115389978164763146323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211078198054445543089/100000000000000000000)
  centralHi := (21107819805444554309/10000000000000000000)
  directionLo := (21306019644874543639/10000000000000000000)
  directionHi := (213060196448745436391/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree055.table
  base := (-6863233978374539729443934760764979090001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-18211697618264510711155734199410000000000000)
      constant := (112050319580152034228022833804248797991786031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree055.table
  base := (-6864800492196426446827004212038305805183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-18729931292555974577627996817810000000000000)
      constant := (120106759190345055889916356572569964259228673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21306019644874543639/10000000000000000000)
  centralHi := (213060196448745436391/100000000000000000000)
  directionLo := (215023926407375085577/100000000000000000000)
  directionHi := (107511963203687542789/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree056.table
  base := (-6913865035140833382146654995029629062251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-2651475363515148706942958695710000000000000)
      constant := (16749776014636937256781924172658200321703683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree056.table
  base := (-6915270207649924245153400754138627792859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-2726854807048452542066196894750000000000000)
      constant := (17944163764171749681681356125123398041448947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215023926407375085577/100000000000000000000)
  centralHi := (107511963203687542789/50000000000000000000)
  directionLo := (216969883957452758483/100000000000000000000)
  directionHi := (54242470989363189621/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree057.table
  base := (-3481241280364136340247158702776163298631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2100995274549730131782854171170000000000000)
      constant := (13617434642730507598328694537346423970607458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree057.table
  base := (-870467826630687742113506940101500902047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1080335333673464500627708872705000000000000)
      constant := (7290413604210474531028255909585952408789092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216969883957452758483/100000000000000000000)
  centralHi := (54242470989363189621/25000000000000000000)
  directionLo := (21889854307732789271/10000000000000000000)
  directionHi := (218898543077327892711/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree058.table
  base := (-7009100990753650275086369874418357537631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-19257587397289101423490664211090000000000000)
      constant := (127975701331537006960247970042783538933142561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree058.table
  base := (-219069705217232320889425186476241265987/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-9902044181452777114067070577065000000000000)
      constant := (68480801867223227390894318501502774644761552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21889854307732789271/10000000000000000000)
  centralHi := (218898543077327892711/100000000000000000000)
  directionLo := (110405178522389784587/50000000000000000000)
  directionHi := (8832414281791182767/4000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree059.table
  base := (-3526866544674781516302244201750930333601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-19606217323630631660935640881650000000000000)
      constant := (133504750082503599559483054777166115011875262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree059.table
  base := (-7054745402385605451628817275540656758751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-20162140719688747444969522599570000000000000)
      constant := (142811577944428005004916781759409133324517281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110405178522389784587/50000000000000000000)
  centralHi := (8832414281791182767/4000000000000000000)
  directionLo := (44541151936208068181/20000000000000000000)
  directionHi := (111352879840520170453/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree060.table
  base := (-1774097536290278320270164116609756393757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2217205249996906877597846394690000000000000)
      constant := (15460445914760215004744951403600389721412652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree060.table
  base := (-3548648555164722396555904395611572699509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1140010726470663370100272446945000000000000)
      constant := (8265407102862661072755129386635296439516531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44541151936208068181/20000000000000000000)
  centralHi := (111352879840520170453/50000000000000000000)
  directionLo := (224585166500317987359/100000000000000000000)
  directionHi := (1403657290626987421/625000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree061.table
  base := (-3568541072117370638369699457262406038997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-20303477176313692135825594222770000000000000)
      constant := (144893451147933692032957354473706020862441814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree061.table
  base := (-7137894501061451714059868872637010437683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-20878245433255133878640285490450000000000000)
      constant := (154858818487750773493273753108793705572836173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224585166500317987359/100000000000000000000)
  centralHi := (1403657290626987421/625000000000000000)
  directionLo := (226448975773443965361/100000000000000000000)
  directionHi := (113224487886721982681/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree062.table
  base := (-7175817922544973150377285462323520482767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-20652107102655222373270570893330000000000000)
      constant := (150753028757795976317109845103967947203897777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree062.table
  base := (-7176545346005683713321626765451579906273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-21236297790038327095475666935890000000000000)
      constant := (161056019008314543343030844731422679352002463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226448975773443965361/100000000000000000000)
  centralHi := (113224487886721982681/50000000000000000000)
  directionLo := (228297569513361379461/100000000000000000000)
  directionHi := (114148784756680689731/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree063.table
  base := (-7212605300572823491741646823451378746567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-333345032206297660487548374030000000000000)
      constant := (2487662143221264142673886966997563138966279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree063.table
  base := (-7213256502459188381056826109781399293967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (968)
      previous := (418)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-342767462647960639877953148910000000000000)
      constant := (2656649241215987729738406052693771844480079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228297569513361379461/100000000000000000000)
  centralHi := (114148784756680689731/50000000000000000000)
  directionLo := (115065657194679866799/50000000000000000000)
  directionHi := (230131314389359733599/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree064.table
  base := (-1811862800514841589866104400843079289399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-21349366955338282848160524234450000000000000)
      constant := (162802482463036363108282307475255273201501476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree064.table
  base := (-45300212645455328975874310412707305921/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-10976201251802356764573214913385000000000000)
      constant := (86898722014431827101863689468797176223964080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115065657194679866799/50000000000000000000)
  centralHi := (230131314389359733599/100000000000000000000)
  directionLo := (7248455080507928537/3125000000000000000)
  directionHi := (46390112515250742637/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree065.table
  base := (-291214470352153599707185468636620774993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-21697996881679813085605500905010000000000000)
      constant := (168992306740974966105469130318206303601319575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree065.table
  base := (-1820220813326721711257353012781621098737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-11155227430193953372990905636105000000000000)
      constant := (90170811645666825044590037775264491718225694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/3125000000000000000)
  centralHi := (46390112515250742637/20000000000000000000)
  directionLo := (233755652544076137469/100000000000000000000)
  directionHi := (23375565254407613747/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree066.table
  base := (-3655671201576377577289962504142611910313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2449625200891260369227830841730000000000000)
      constant := (19476907366196905417878203923016216295103934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree066.table
  base := (-7311808914260381299560670964989935530571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2518723024130122218090799190850000000000000)
      constant := (20777935693732613917953717107499438431018189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233755652544076137469/100000000000000000000)
  centralHi := (23375565254407613747/10000000000000000000)
  directionLo := (235546909793300213467/100000000000000000000)
  directionHi := (58886727448325053367/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree067.table
  base := (-7340397949630750398346364408343657726801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-22395256734362873560495454246130000000000000)
      constant := (181702042018579620657010708270389022482326831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree067.table
  base := (-1835203794819997334258718035803561003259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-11513279786977146589826287081545000000000000)
      constant := (96888410661212106312594514311966332756130058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235546909793300213467/100000000000000000000)
  centralHi := (58886727448325053367/25000000000000000000)
  directionLo := (11866232377005703071/5000000000000000000)
  directionHi := (237324647540114061421/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree068.table
  base := (-7367532666991896747769379070845623186143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-22743886660704403797940430916690000000000000)
      constant := (188221916966712473900365555737713721574198433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree068.table
  base := (-1841976434645576049379034985874555184629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-11692305965368743198243977804265000000000000)
      constant := (100333904440678026805091144972067780944414998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11866232377005703071/5000000000000000000)
  centralHi := (237324647540114061421/100000000000000000000)
  directionLo := (239089167355833222067/100000000000000000000)
  directionHi := (59772291838958305517/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree069.table
  base := (-3696375170909405765178453865542185296441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2565835176338437115042823065250000000000000)
      constant := (21650197345691588924232152096526792568539038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree069.table
  base := (-184827096429372160165279444528017039639/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1319036904862259978517963169665000000000000)
      constant := (11537465053420780027246124004047889710384020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239089167355833222067/100000000000000000000)
  centralHi := (59772291838958305517/25000000000000000000)
  directionLo := (12042037988207382919/5000000000000000000)
  directionHi := (240840759764147658381/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree070.table
  base := (-1854013583665930048243087973430319681117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-3348735216198209181832912036830000000000000)
      constant := (28798800873440473873083043870210034963226644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree070.table
  base := (-927044053203693951754099992610100800397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-1721479760307419487868479892815000000000000)
      constant := (15342606863599902639444478222410291384699604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12042037988207382919/5000000000000000000)
  centralHi := (240840759764147658381/100000000000000000000)
  directionLo := (242579704799552728083/100000000000000000000)
  directionHi := (60644926199888182021/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree071.table
  base := (-7437447629608275060259688913611318986977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-23789776439728994510275360928370000000000000)
      constant := (208441395131469446204329424284481674940688287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree071.table
  base := (-7437714004746176146876085981235869808917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-24458769001087066046994099944850000000000000)
      constant := (222034174104015133853319308299264832728408427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242579704799552728083/100000000000000000000)
  centralHi := (60644926199888182021/25000000000000000000)
  directionLo := (61076568132500906379/25000000000000000000)
  directionHi := (244306272530003625517/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree072.table
  base := (-7456932878015562566116917495977667420027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2682045151785613860857815288770000000000000)
      constant := (23933459182235844171132507065193848667768093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree072.table
  base := (-1491434172968788734287151522179850186621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2757424595318917695981053487810000000000000)
      constant := (25487488443502965691355146796393430338500695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61076568132500906379/25000000000000000000)
  centralHi := (244306272530003625517/100000000000000000000)
  directionLo := (246020723546555450101/100000000000000000000)
  directionHi := (123010361773277725051/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree073.table
  base := (-7474512437156615890949317801222023815883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-24487036292412054985165314269490000000000000)
      constant := (222470809284034040426142168041624787474760373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree073.table
  base := (-3737362510163959116867992995342776822111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-12587436857326726240332431417865000000000000)
      constant := (118428076878879804930091899190649518793041441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246020723546555450101/100000000000000000000)
  centralHi := (123010361773277725051/50000000000000000000)
  directionLo := (247723309422502513317/100000000000000000000)
  directionHi := (123861654711251256659/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree074.table
  base := (-1498037680862684406483774414789929598697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-24835666218753585222610290940050000000000000)
      constant := (229650416739091568468457830120283847113858035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree074.table
  base := (-3745189130050290559188774618495012764697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-12766463035718322848750122140585000000000000)
      constant := (122220220151279970774350625798283294336917607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247723309422502513317/100000000000000000000)
  centralHi := (123861654711251256659/50000000000000000000)
  directionLo := (249414273144307404351/100000000000000000000)
  directionHi := (3897098017879803193/1562500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree075.table
  base := (-7503962646889578950505778997215207461473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2798255127232790606672807512290000000000000)
      constant := (26326660843730033484886460138853093509490407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree075.table
  base := (-469008260894949648447530838262618283647/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1438387690456657717463090318145000000000000)
      constant := (14007791628588528511782905443984482695293384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249414273144307404351/100000000000000000000)
  centralHi := (3897098017879803193/1562500000000000000)
  directionLo := (251093849516409782017/100000000000000000000)
  directionHi := (125546924758204891009/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree076.table
  base := (-939479603624660827249121241894633638867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-25532926071436645697500244281170000000000000)
      constant := (244339395242608917420727646845541592698695016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree076.table
  base := (-300639527117575962443200476384218050799/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-26249030785003032131171007172050000000000000)
      constant := (259955575177901385495143014988815963909469225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251093849516409782017/100000000000000000000)
  centralHi := (125546924758204891009/50000000000000000000)
  directionLo := (252762265541824300477/100000000000000000000)
  directionHi := (126381132770912150239/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree077.table
  base := (-1505162486986850192360791532102991411077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-3697365142539739419277888707390000000000000)
      constant := (35978393399289974544963846387553019349596705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree077.table
  base := (-94074344142903877559876113942724558151/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-1900505938699016096286170615535000000000000)
      constant := (19134743777833835917794695611354007021135320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252762265541824300477/100000000000000000000)
  centralHi := (126381132770912150239/50000000000000000000)
  directionLo := (254419740780274279697/100000000000000000000)
  directionHi := (127209870390137139849/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree078.table
  base := (-7533890789915467712135630556775328773167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-2914465102679967352487799735810000000000000)
      constant := (28829779776783855165876058317512080011033353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree078.table
  base := (-3767005679507823217874687724552681615097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1498063083253856586935653892385000000000000)
      constant := (15329597665993907779651060288182267407742223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254419740780274279697/100000000000000000000)
  centralHi := (127209870390137139849/50000000000000000000)
  directionLo := (256066487685460743423/100000000000000000000)
  directionHi := (1000259717521331029/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree079.table
  base := (-1508014615676393054634083607357800588289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-26578815850461236409835174292850000000000000)
      constant := (267197183129637099718940384940149447325404795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree079.table
  base := (-7540180664698351901882273994705795457923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-27323187855352611781677151508370000000000000)
      constant := (284094606487639797725811099033242697827503613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256066487685460743423/100000000000000000000)
  centralHi := (1000259717521331029/390625000000000000)
  directionLo := (128851355961466775101/50000000000000000000)
  directionHi := (257702711922933550203/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree080.table
  base := (-7544360360170745217188778361795124645943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-26927445776802766647280150963410000000000000)
      constant := (275036245004283972252533366121635150280252233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree080.table
  base := (-235764260825064008581174707202221560113/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-13840620106067902499256266476905000000000000)
      constant := (146185977412535579755790114783030122046584048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128851355961466775101/50000000000000000000)
  centralHi := (257702711922933550203/100000000000000000000)
  directionLo := (51865722533982204993/20000000000000000000)
  directionHi := (129664306334955512483/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree081.table
  base := (-754675358479676998073718263008875430081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3030675078127144098302791959330000000000000)
      constant := (31442799982930047575890058290325859353342790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree081.table
  base := (-7546839208390895237143487924985168068657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3115476952102110912816434933250000000000000)
      constant := (33418311089784441734246057727891540881722263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51865722533982204993/20000000000000000000)
  centralHi := (129664306334955512483/50000000000000000000)
  directionLo := (65236095724571356833/25000000000000000000)
  directionHi := (260944382898285427333/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree082.table
  base := (-943406700508548100771671623333729264589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-27624705629485827122170104304530000000000000)
      constant := (291044044275069145243453981840537428390770072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree082.table
  base := (-1509465994442702342716468362468981191073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-28397344925702191432183295844690000000000000)
      constant := (309273138572779777506110398905703068263156315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65236095724571356833/25000000000000000000)
  centralHi := (260944382898285427333/100000000000000000000)
  directionLo := (6563755241048814781/2500000000000000000)
  directionHi := (262550209641952591241/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree083.table
  base := (-7545861183231562227435123976544312317227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-27973335555827357359615080975090000000000000)
      constant := (299212775253118858446664710635320624412926037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree083.table
  base := (-7545929286336054018520669391085327498229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-28755397282485384649018677290130000000000000)
      constant := (317896968545468390792594601266012335159529099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6563755241048814781/2500000000000000000)
  centralHi := (262550209641952591241/100000000000000000000)
  directionLo := (66036568562378524483/25000000000000000000)
  directionHi := (264146274249514097933/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree084.table
  base := (-1885644252703853636049121865571030965267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-449555007653474406302540597550000000000000)
      constant := (4880815715043611445638673002456100196752716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree084.table
  base := (-7542637734623954016974436887611428038941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (968)
      previous := (418)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-462118248242358378823080297390000000000000)
      constant := (5184702974742284387228869153640480033546717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66036568562378524483/25000000000000000000)
  centralHi := (264146274249514097933/100000000000000000000)
  directionLo := (265732752623318478719/100000000000000000000)
  directionHi := (415207425973935123/156250000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree085.table
  base := (-29442975419262394878704962530772237047/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-28670595408510417834505034316210000000000000)
      constant := (315879886196146055970512240758708437737076992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree085.table
  base := (-7537455843810832483097099331546538984201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-29471501996051771082689440181010000000000000)
      constant := (335491093072060613461967802133141786771706231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265732752623318478719/100000000000000000000)
  centralHi := (415207425973935123/156250000000000000)
  directionLo := (33413726930716670899/12500000000000000000)
  directionHi := (267309815445733367193/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree086.table
  base := (-7530335832958965460035228701239341758223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-29019225334851948071950010986770000000000000)
      constant := (324378261474959536694664280728111052561612913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree086.table
  base := (-7530384090076405619896621691823279892769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-29829554352834964299524821626450000000000000)
      constant := (344461383645401188382503124665693402105599839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33413726930716670899/12500000000000000000)
  centralHi := (267309815445733367193/100000000000000000000)
  directionLo := (268877628393472505833/100000000000000000000)
  directionHi := (134438814196736252917/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree087.table
  base := (-150427597886819069540815449178908897499/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3263095029021497589932776406370000000000000)
      constant := (36998501541480580331751509212250058810147050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree087.table
  base := (-300856916193620786220568624455040559633/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3354178523290906390706689230210000000000000)
      constant := (39283017490720030164170250585133177830046175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268877628393472505833/100000000000000000000)
  centralHi := (134438814196736252917/50000000000000000000)
  directionLo := (135218176170369706209/50000000000000000000)
  directionHi := (270436352340739412419/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree088.table
  base := (-3755267175292739296362392051190700512331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-29716485187535008546839964327890000000000000)
      constant := (341704641569042107617806967774648219333116522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree088.table
  base := (-7510572679867536480826460900759600098967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-30545659066401350733195584517330000000000000)
      constant := (362748412830385110402166048666565147207199977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135218176170369706209/50000000000000000000)
  centralHi := (270436352340739412419/100000000000000000000)
  directionLo := (271986143551892750981/100000000000000000000)
  directionHi := (135993071775946375491/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree089.table
  base := (-749779961857458011471114221338096423723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-30065115113876538784284940998450000000000000)
      constant := (350532642907505376578835261230005952942434130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree089.table
  base := (-7497833771763938715320901143341299980041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-30903711423184543950030965962770000000000000)
      constant := (372065148471744575639658444384408380379217271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271986143551892750981/100000000000000000000)
  centralHi := (135993071775946375491/50000000000000000000)
  directionLo := (273527153864286515913/100000000000000000000)
  directionHi := (136763576932143257957/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree090.table
  base := (-935397009707051590971296670976162348087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3379305004468674335747768629890000000000000)
      constant := (39941168487009133769443804810746099235949064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree090.table
  base := (-7483206505942037468586820512941008470923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3473529308885304129651816378690000000000000)
      constant := (42388595894333022710672174837093015264322957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273527153864286515913/100000000000000000000)
  centralHi := (136763576932143257957/50000000000000000000)
  directionLo := (275059530861890566679/100000000000000000000)
  directionHi := (6876488271547264167/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree091.table
  base := (-3733332036897261972337758805564711345237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-4394624995222799894167842048510000000000000)
      constant := (52645465803234752796869674004904617334501242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree091.table
  base := (-3733345590056942587108668577120899490831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-2258558295482209313121552060975000000000000)
      constant := (27931789670037418611600596442757449988698823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275059530861890566679/100000000000000000000)
  centralHi := (6876488271547264167/2500000000000000000)
  directionLo := (138291709020126716633/50000000000000000000)
  directionHi := (276583418040253433267/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree092.table
  base := (-7448263923237509669228334705530234085963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-31111004892901129496619871010130000000000000)
      constant := (377675874370997896395926500946730500912812853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree092.table
  base := (-7448288067371773926485724159685145030753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-31977868493534123600537110299090000000000000)
      constant := (400708224382421236816564153474809659372941343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138291709020126716633/50000000000000000000)
  centralHi := (276583418040253433267/100000000000000000000)
  directionLo := (139049477481664640317/50000000000000000000)
  directionHi := (55619790992665856127/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree093.table
  base := (-7427975915765115035732106309834992672587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3495514979915851081562760853410000000000000)
      constant := (42993706275334475104495651903337768231389133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree093.table
  base := (-1485599483780981799306110055969822601689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3592880094479701868596943527170000000000000)
      constant := (45609652117524375270818667110156541163275755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139049477481664640317/50000000000000000000)
  centralHi := (55619790992665856127/20000000000000000000)
  directionLo := (139803138706327071811/50000000000000000000)
  directionHi := (279606277412654143623/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree094.table
  base := (-7405800317560271618424504081557640381253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-31808264745584189971509824351250000000000000)
      constant := (396320705887200352793541497775587725326806843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree094.table
  base := (-7405819466395875309153482058459110082493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-32693973207100510034207873189970000000000000)
      constant := (420380988486870102858282087236355792082585283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139803138706327071811/50000000000000000000)
  centralHi := (279606277412654143623/100000000000000000000)
  directionLo := (281105517529322725239/100000000000000000000)
  directionHi := (7027637938233068131/2500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree095.table
  base := (-7381737373750758195819158707661273702397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-32156894671925720208954801021810000000000000)
      constant := (405807921625655972983247792686817404675186307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree095.table
  base := (-3690877212067631421775439069701177389699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-16526012781941851625521627317705000000000000)
      constant := (215195290909677030725938027876031026940284669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281105517529322725239/100000000000000000000)
  centralHi := (7027637938233068131/2500000000000000000)
  directionLo := (17662300246824120263/6250000000000000000)
  directionHi := (282596803949185924209/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree096.table
  base := (-57467088364523826576251272775126341383/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3611724955363027827377753076930000000000000)
      constant := (46156111421678137011139171981109668281612416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree096.table
  base := (-1838950622722049579923237298864527999873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1856115440037049803771035337825000000000000)
      constant := (24473091570348470292588230187681486304112014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17662300246824120263/6250000000000000000)
  centralHi := (282596803949185924209/100000000000000000000)
  directionLo := (142040130965830290927/50000000000000000000)
  directionHi := (56816052386332116371/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree097.table
  base := (-1831987584448599687320355552688343012921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-32854154524608780683844754362930000000000000)
      constant := (425111948563999910714124192249674866326866204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree097.table
  base := (-91599548144280859560175850157156782123/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-16884065138725044842357008763145000000000000)
      constant := (225378093546902843795662562263774789270152520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142040130965830290927/50000000000000000000)
  centralHi := (56816052386332116371/20000000000000000000)
  directionLo := (71389003370629124329/25000000000000000000)
  directionHi := (285556013482516497317/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree098.table
  base := (-3649113324808600516404575441000541787839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-4743254921564330131612818719070000000000000)
      constant := (62132679737218956303283583062555385612590574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree098.table
  base := (-1824559669641087613770292233525095510413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-2437584473873805921539242783695000000000000)
      constant := (32936585544102505563284316913652541691191658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71389003370629124329/25000000000000000000)
  centralHi := (285556013482516497317/100000000000000000000)
  directionLo := (287024177470981358451/100000000000000000000)
  directionHi := (71756044367745339613/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree099.table
  base := (-7266616427102179656150239381889623398201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3727934930810204573192745300450000000000000)
      constant := (49428381207379211969413963020771676081393359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree099.table
  base := (-1816656783321278808078625902496794446629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1915790832834248673243598912065000000000000)
      constant := (26199093288713156567242750076132827298073222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287024177470981358451/100000000000000000000)
  centralHi := (71756044367745339613/25000000000000000000)
  directionLo := (288484869741481697031/100000000000000000000)
  directionHi := (36060608717685212129/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree100.table
  base := (-723311983912380798009353829098220051513/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-33900044303633371396179684374610000000000000)
      constant := (454891966011377766750375001542591646155449030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree100.table
  base := (-904141170879802920850014856769847833737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-17421143673899834667610080931305000000000000)
      constant := (241085315615683805475863499230421895791591388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288484869741481697031/100000000000000000000)
  centralHi := (36060608717685212129/12500000000000000000)
  directionLo := (7248455080507928537/2500000000000000000)
  directionHi := (289938203220317141481/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree101.table
  base := (-719773704368465257958082975887593659079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-34248674229974901633624661045170000000000000)
      constant := (465038362968315084463989151153076407671154490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree101.table
  base := (-1799436380541595575571254973969177316643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-17600169852291431276027771654025000000000000)
      constant := (246436526578035815832910532153777670460487866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7248455080507928537/2500000000000000000)
  centralHi := (289938203220317141481/100000000000000000000)
  directionLo := (145692144008772981989/50000000000000000000)
  directionHi := (291384288017545963979/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree102.table
  base := (-1432093637800978699153389610772610775877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-3844144906257381319007737523970000000000000)
      constant := (52810513460993218475802730978616393239191215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree102.table
  base := (-3580237866454956807820857551740375504417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-1975466225631447542716162486305000000000000)
      constant := (27982830246563703478558039622032494402552103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145692144008772981989/50000000000000000000)
  centralHi := (291384288017545963979/100000000000000000000)
  directionLo := (292823231524342070353/100000000000000000000)
  directionHi := (146411615762171035177/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree103.table
  base := (-1424262682897828469238764464461379616907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-34945934082657962108514614386290000000000000)
      constant := (485660739999952508695057367724088921502480585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree103.table
  base := (-7121320126197191033912319222224735063581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-35916444418149248985726306198930000000000000)
      constant := (514624304573814782273767791704020026532647011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292823231524342070353/100000000000000000000)
  centralHi := (146411615762171035177/50000000000000000000)
  directionLo := (294255138506067042083/100000000000000000000)
  directionHi := (73563784626516760521/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree104.table
  base := (-7080272851584792142400049440166233428693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-35294564008999492345959591056850000000000000)
      constant := (496136718999641008839690826902020219521517483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree104.table
  base := (-7080278822342259318439455814840644489197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-36274496774932442202561687644370000000000000)
      constant := (525673133085549546987221426909377482022377107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294255138506067042083/100000000000000000000)
  centralHi := (73563784626516760521/25000000000000000000)
  directionLo := (147840055595642751097/50000000000000000000)
  directionHi := (59136022238257100439/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree105.table
  base := (-1759336656136116851163590353264925865461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-565764983100651152117532821070000000000000)
      constant := (8043215200870568253891719984302238681903828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree105.table
  base := (-1759337983916122484747791635197529858997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (-290734516918378058884103722935000000000000)
      constant := (4260614519996963265007113186240111237766378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147840055595642751097/50000000000000000000)
  centralHi := (59136022238257100439/20000000000000000000)
  directionLo := (297098249356937842747/100000000000000000000)
  directionHi := (74274562339234460687/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree106.table
  base := (-6992534851103673264298666126206553608441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-35991823861682552820849544397970000000000000)
      constant := (517418255498274662295223931654716188728097671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree106.table
  base := (-3496269787519125352181968127815885512821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-18495300744249414318116225267625000000000000)
      constant := (274058596721947944825839523491468750399613451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297098249356937842747/100000000000000000000)
  centralHi := (74274562339234460687/25000000000000000000)
  directionLo := (2332106643827118219/781250000000000000)
  directionHi := (298509650409871132033/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree107.table
  base := (-3472918821541722382317150632980941757671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-36340453788024083058294521068530000000000000)
      constant := (528223812086109907652964535555902284327607602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree107.table
  base := (-1736460461095260442703310137516630198657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-18674326922641010926533915990345000000000000)
      constant := (279756212222968271824695900419967989483060734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2332106643827118219/781250000000000000)
  centralHi := (298509650409871132033/100000000000000000000)
  directionLo := (299914409464916733127/100000000000000000000)
  directionHi := (37489301183114591641/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree108.table
  base := (-3448627553463326132880953202559106086669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4076564857151734810637721971010000000000000)
      constant := (59904358555097753734351192472242868431557942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree108.table
  base := (-6897258843087361144768177274489162942867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4189634022451690563322579269570000000000000)
      constant := (63447013570138063421835270407670279142195653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299914409464916733127/100000000000000000000)
  centralHi := (37489301183114591641/12500000000000000000)
  directionLo := (301312619419691738421/100000000000000000000)
  directionHi := (150656309709845869211/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree109.table
  base := (-6846787344175607859307372676731205450101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-37037713640707143533184474409650000000000000)
      constant := (550164499824562853472149359830468845568549131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree109.table
  base := (-1711697666603673150084109866599935336879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-19032379279424204143369297435785000000000000)
      constant := (291324643060868508996811255902194713295854498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301312619419691738421/100000000000000000000)
  centralHi := (150656309709845869211/50000000000000000000)
  directionLo := (75676092756572672327/25000000000000000000)
  directionHi := (302704371026290689309/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree110.table
  base := (-339721722594886261841857480879097757349/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-37386343567048673770629451080210000000000000)
      constant := (561299630186898552300103180085267220021636380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree110.table
  base := (-6794437405827243484304881730040232073099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-38422810915631601503573976317010000000000000)
      constant := (594390916054398446281310009321770318901870069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75676092756572672327/25000000000000000000)
  centralHi := (302704371026290689309/100000000000000000000)
  directionLo := (7602243824000603629/2500000000000000000)
  directionHi := (304089752960024145161/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree111.table
  base := (-1348039304613039522802378554353079357273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4192774832598911556452714194530000000000000)
      constant := (63616068634875582802229450128896460017213035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree111.table
  base := (-6740199149302386552730577562073390979153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4308984808046088302267706418050000000000000)
      constant := (67360890175560518132309933501435634578193527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7602243824000603629/2500000000000000000)
  centralHi := (304089752960024145161/100000000000000000000)
  directionLo := (152734425942675717189/50000000000000000000)
  directionHi := (305468851885351434379/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree112.table
  base := (-6684073646893962809248061070210358276327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-5440514774247390606502772060190000000000000)
      constant := (83414208864487125004391435365430726857322591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree112.table
  base := (-3342037990802083834311797587662982014437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-2795636830656999138374624229135000000000000)
      constant := (44158612311589083620840980545795089197814221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152734425942675717189/50000000000000000000)
  centralHi := (305468851885351434379/100000000000000000000)
  directionLo := (38355219064893288933/12500000000000000000)
  directionHi := (61368350503829262293/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree113.table
  base := (-3313032954573305285599008759799767034301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-38432233346073264482964381091890000000000000)
      constant := (595364162859095723019726940505584449281718662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree113.table
  base := (-1656516996131930030919269117292228743223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-19748483992990590577040060326665000000000000)
      constant := (315154299038180542374766453753899288236295826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38355219064893288933/12500000000000000000)
  centralHi := (61368350503829262293/20000000000000000000)
  directionLo := (308208537691426210417/100000000000000000000)
  directionHi := (154104268845713105209/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree114.table
  base := (-6566173392403345177465232911932879940871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4308984808046088302267706418050000000000000)
      constant := (67437635534352995378801950492147599946075889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree114.table
  base := (-1641543809279491985188633875168444083411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2214167796820243020606416783265000000000000)
      constant := (35695116022703172328740091878911432318431498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308208537691426210417/100000000000000000000)
  centralHi := (154104268845713105209/50000000000000000000)
  directionLo := (77392322100917070801/25000000000000000000)
  directionHi := (61913857680733656641/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree115.table
  base := (-6504396176304637744810769383994265344679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-39129493198756324957854334433010000000000000)
      constant := (618623132585560551336787233708351760846969049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree115.table
  base := (-6504397815865597215844462736213952811431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-40213072699547567587750883544210000000000000)
      constant := (654831043055543689080161647917916821291430361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77392322100917070801/25000000000000000000)
  centralHi := (61913857680733656641/20000000000000000000)
  directionLo := (155462041942414201501/50000000000000000000)
  directionHi := (310924083884828403003/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree116.table
  base := (-1288146867553756029498580393136420416951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-39478123125097855195299311103570000000000000)
      constant := (630417400882957801353504884748987736825607405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree116.table
  base := (-64407357948829197273223458434455462179/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-20285562528165380402293132494825000000000000)
      constant := (333632730861434540394840289623702313530577450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155462041942414201501/50000000000000000000)
  centralHi := (310924083884828403003/100000000000000000000)
  directionLo := (62454600329034551793/20000000000000000000)
  directionHi := (156136500822586379483/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree117.table
  base := (-637518795118717935928858451626625182359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4425194783493265048082698641570000000000000)
      constant := (71369058267345468242272197520421582945796810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree117.table
  base := (-31875946230309704182774330989539648929/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2273843189617441890078980357505000000000000)
      constant := (37767519118071883764811893857186301482231100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62454600329034551793/20000000000000000000)
  centralHi := (156136500822586379483/50000000000000000000)
  directionLo := (156808058764012769599/50000000000000000000)
  directionHi := (313616117528025539199/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree118.table
  base := (-6307757088599901612280429218017423535153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-40175382977780915670189264444690000000000000)
      constant := (654335502869087766942486024761338845988977743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree118.table
  base := (-6307758239216668991262803905134089046067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-41287229769897147238257027880530000000000000)
      constant := (692480689985726370481958402224902800576160077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156808058764012769599/50000000000000000000)
  centralHi := (313616117528025539199/100000000000000000000)
  directionLo := (157476752879765230327/50000000000000000000)
  directionHi := (62990701151906092131/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree119.table
  base := (-311922090992684243978486312128932813659/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-5789144700588920843947748730750000000000000)
      constant := (95208476570667393803482086470052901893106940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree119.table
  base := (-311922142110573120268119128881304790581/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-2974663009048595746792314951855000000000000)
      constant := (50375821359629487941762859008288001837405730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157476752879765230327/50000000000000000000)
  centralHi := (62990701151906092131/20000000000000000000)
  directionLo := (316285238996518530641/100000000000000000000)
  directionHi := (158142619498259265321/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree120.table
  base := (-6167242212744381318990944096217141519731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4541404758940441793897690865090000000000000)
      constant := (75410335945975494001296723752168240589798629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree120.table
  base := (-385452695067312234655874424678898289251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2333518582414640759551543931745000000000000)
      constant := (39897653945026530115953458823932846835522472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316285238996518530641/100000000000000000000)
  centralHi := (158142619498259265321/50000000000000000000)
  directionLo := (79402847093142347173/25000000000000000000)
  directionHi := (317611388372569388693/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree121.table
  base := (-3047079166572782235363178307063700674859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-41221272756805506382524194456370000000000000)
      constant := (691036565164958621723390305346883344042969258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree121.table
  base := (-6094159140115242502261015017947134840897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-42361386840246726888763172216850000000000000)
      constant := (731169505657505970512363259505057821816479807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79402847093142347173/25000000000000000000)
  centralHi := (317611388372569388693/100000000000000000000)
  directionLo := (79733005885587213907/25000000000000000000)
  directionHi := (318932023542348855629/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree122.table
  base := (-752398780640604457788880386427682788327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-41569902683147036619969171126930000000000000)
      constant := (703489960693924974090547250300178216105041096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree122.table
  base := (-601919096199470368694679693390228882381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-21359719598514960052799276831145000000000000)
      constant := (372148351363583417919668222491520907829149055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79733005885587213907/25000000000000000000)
  centralHi := (318932023542348855629/100000000000000000000)
  directionLo := (320247212724300886929/100000000000000000000)
  directionHi := (32024721272430088693/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree123.table
  base := (-5942338011049187131790653270429690587243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4657614734387618539712683088610000000000000)
      constant := (79561467761460434546704240533565506451025837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree123.table
  base := (-1485584661959242237678904806877361341067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2393193975211839629024107505985000000000000)
      constant := (42085520109826030487685098738269167297178906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320247212724300886929/100000000000000000000)
  centralHi := (32024721272430088693/10000000000000000000)
  directionLo := (321557022741767969481/100000000000000000000)
  directionHi := (160778511370883984741/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree124.table
  base := (-45809388216254867898478296833687912913/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-42267162535830097094859124468050000000000000)
      constant := (728726312401451037495969950558527862226982784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree124.table
  base := (-1465900564323891976933032143097801726267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-21717771955298153269634658276585000000000000)
      constant := (385448741584923125145364886887429649896892554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321557022741767969481/100000000000000000000)
  centralHi := (160778511370883984741/50000000000000000000)
  directionLo := (8071537976565252397/2500000000000000000)
  directionHi := (322861519062610095881/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree125.table
  base := (-5782981346263101894944047762324464920259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-42615792462171627332304101138610000000000000)
      constant := (741509268103707083106490081830709198731492029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree125.table
  base := (-1156596369725591506975769905311323541727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-43793596267379499756104697998610000000000000)
      constant := (784371066074876093635283694470346784314427685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8071537976565252397/2500000000000000000)
  centralHi := (322861519062610095881/100000000000000000000)
  directionLo := (162080382918694390603/50000000000000000000)
  directionHi := (324160765837388781207/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree126.table
  base := (-5700477032601740523345963692057383494527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-681974958547827897932525044590000000000000)
      constant := (11974636138579103785068494126510384839844799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree126.table
  base := (-1425119369690348072939159414476653739569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (-350409909715576928356667297175000000000000)
      constant := (6333016749730268300490775743065941628814306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162080382918694390603/50000000000000000000)
  centralHi := (324160765837388781207/100000000000000000000)
  directionLo := (81363706484044784431/25000000000000000000)
  directionHi := (13018193037447165509/4000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree127.table
  base := (-224643552285404593244116186646272004419/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-43313052314854687807194054479730000000000000)
      constant := (767404738057775695986379005429228660361524725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree127.table
  base := (-175502787604791766231444725362057462259/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-22254850490472943094887730444745000000000000)
      constant := (405832308061177455500400615573882902916704464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81363706484044784431/25000000000000000000)
  centralHi := (13018193037447165509/4000000000000000000)
  directionLo := (408429701230087223/125000000000000000)
  directionHi := (326743760984069778401/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree128.table
  base := (-5529816725001393820144517902618287647051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-43661682241196218044639031150290000000000000)
      constant := (780517251866740162919022938399708016328854581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree128.table
  base := (-2764908538423500954377604581551331462771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-22433876668864539703305421167465000000000000)
      constant := (412742291413907150925441298040462765424261901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408429701230087223/125000000000000000)
  centralHi := (326743760984069778401/100000000000000000000)
  directionLo := (328027631395407266801/100000000000000000000)
  directionHi := (164013815697703633401/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree129.table
  base := (-5441660840098962058097079636503294338999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-4890034685281972031342667535650000000000000)
      constant := (88193290882606027878704248722737047196501441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree129.table
  base := (-5441661152522525220315278720648419956219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5025089521612474735938469308930000000000000)
      constant := (93268890041213679512178985835164046799307421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328027631395407266801/100000000000000000000)
  centralHi := (164013815697703633401/50000000000000000000)
  directionLo := (13172259856273558249/4000000000000000000)
  directionHi := (164653248203419478113/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree130.table
  base := (-1337905301285527505332029720698667865051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-44358942093879278519528984491410000000000000)
      constant := (807071836078694941053622183083537948974450324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree130.table
  base := (-1070324296508848375381339965217211224933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-45583858051295465840281605225810000000000000)
      constant := (853470898544641104983812448745164443241204615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13172259856273558249/4000000000000000000)
  centralHi := (164653248203419478113/50000000000000000000)
  directionLo := (330580414109205352963/100000000000000000000)
  directionHi := (82645103527301338241/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree131.table
  base := (-5259697871712306427477225613490033555739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-44707572020220808756973961161970000000000000)
      constant := (820513906067735384014563239537563056817271909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree131.table
  base := (-2629849059002229287240211773475667591127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-22970955204039329528558493335625000000000000)
      constant := (433818623573091452348628999989970075330816937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330580414109205352963/100000000000000000000)
  centralHi := (82645103527301338241/25000000000000000000)
  directionLo := (66369888295666117329/20000000000000000000)
  directionHi := (165924720739165293323/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree132.table
  base := (-5165890890305508534821106482241894206411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5006244660729148777157659759170000000000000)
      constant := (92673980856684125048117906573151324654972749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree132.table
  base := (-5165891108964081812044007769975252725369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5144440307206872474883596457410000000000000)
      constant := (97991006219650752983931836552040913548112271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66369888295666117329/20000000000000000000)
  centralHi := (165924720739165293323/50000000000000000000)
  directionLo := (333113634404757164427/100000000000000000000)
  directionHi := (83278408601189291107/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree133.table
  base := (-507020031037591503118139307195235813823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-6486404553271981318837702071870000000000000)
      constant := (121103942972810921531021698027628012935623590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree133.table
  base := (-5070200504490418482536403231676765272743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-6665430731663577927255392794590000000000000)
      constant := (128045189263130654342874762891029274090354719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333113634404757164427/100000000000000000000)
  centralHi := (83278408601189291107/25000000000000000000)
  directionLo := (334373047722468916153/100000000000000000000)
  directionHi := (167186523861234458077/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree134.table
  base := (-1243156545094130181546198645626126461367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-45753461799245399469308891173650000000000000)
      constant := (861499225173983423467427011828329616299337508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree134.table
  base := (-994525270538485746847378417655223795237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-47016067478428238707623131007570000000000000)
      constant := (910829053550411852502947962908412083783521735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334373047722468916153/100000000000000000000)
  centralHi := (167186523861234458077/50000000000000000000)
  directionLo := (335627735236643895643/100000000000000000000)
  directionHi := (83906933809160973911/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree135.table
  base := (-487316854779679210289496051215862119747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5122454636176325522972651982690000000000000)
      constant := (97264522290510261245845212356063048051915730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree135.table
  base := (-609146087594209953569653959371061143833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2631895546400635106914361802945000000000000)
      constant := (51414291217504278638728729562144448142278588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335627735236643895643/100000000000000000000)
  centralHi := (83906933809160973911/25000000000000000000)
  directionLo := (336877749750476981039/100000000000000000000)
  directionHi := (4210971871880962263/1250000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree136.table
  base := (-190873098367909890582458277875740019729/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-46450721651928459944198844514770000000000000)
      constant := (889372026946702553100894056526859696542389975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree136.table
  base := (-2385913797481610087844749218640886373083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-23866086095997312570646946949225000000000000)
      constant := (470100444876094416930589248227734321985233573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336877749750476981039/100000000000000000000)
  centralHi := (4210971871880962263/1250000000000000000)
  directionLo := (16906157154555500351/5000000000000000000)
  directionHi := (338123143091110007021/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree137.table
  base := (-2334301480122346194077202136495876562387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-46799351578269990181643821185330000000000000)
      constant := (903473203989068428915894039982050731847771994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree137.table
  base := (-583575385093071709627138603462123113621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-24045112274388909179064637671945000000000000)
      constant := (477529998440730671805970638009560333448153004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16906157154555500351/5000000000000000000)
  centralHi := (338123143091110007021/100000000000000000000)
  directionLo := (169681983067352728359/50000000000000000000)
  directionHi := (339363966134705456719/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree138.table
  base := (-4563495095737838990438839948810053518251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5238664611623502268787644206210000000000000)
      constant := (101964914618208659905285158655324766398451309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree138.table
  base := (-570436900335377693572448030337890634917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2691570939197833976386925377185000000000000)
      constant := (53890809062551975711619145021493960920006412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169681983067352728359/50000000000000000000)
  centralHi := (339363966134705456719/100000000000000000000)
  directionLo := (34060026883069803487/10000000000000000000)
  directionHi := (340600268830698034871/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree139.table
  base := (-2228251954820500851281812293104799332063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-47496611430953050656533774526450000000000000)
      constant := (932005109496638703524881392505999102902083906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree139.table
  base := (-4456504004551333596714204538266220686093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-48806329262344204791800038234770000000000000)
      constant := (985124588311877368091435835810451370096896883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34060026883069803487/10000000000000000000)
  centralHi := (340600268830698034871/100000000000000000000)
  directionLo := (13673284009010273199/4000000000000000000)
  directionHi := (42729012528157103747/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree140.table
  base := (-2173814722554277231525278315230464924399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-6835034479613511556282678742430000000000000)
      constant := (135205119659438715983692273682428652775731534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree140.table
  base := (-4347629529334082760585448493618582353111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-7023483088446771144090774240030000000000000)
      constant := (142904296038382998494753019430718263805786063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13673284009010273199/4000000000000000000)
  centralHi := (42729012528157103747/12500000000000000000)
  directionLo := (34305950848398924639/10000000000000000000)
  directionHi := (343059508483989246391/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree141.table
  base := (-105921793612770093693176321698548106471/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5354874587070679014602636429730000000000000)
      constant := (106775157306000790869766775609532611401851560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree141.table
  base := (-4236871819250667358467564548808256829633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5502492663990065691718977902850000000000000)
      constant := (112850112758753070555491113215785558738131847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34305950848398924639/10000000000000000000)
  centralHi := (343059508483989246391/100000000000000000000)
  directionLo := (68856508182783288429/20000000000000000000)
  directionHi := (172141270456958221073/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree142.table
  base := (-824846169891584073631503714304985829707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-48542501209977641368868704538130000000000000)
      constant := (975626843745296253399947462104347556209464585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree142.table
  base := (-2062115457888575319719192473982186523569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-24940243166346892221153091285545000000000000)
      constant := (515543707913774404832146284207314701687954639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68856508182783288429/20000000000000000000)
  centralHi := (172141270456958221073/50000000000000000000)
  directionLo := (172750621992374319893/50000000000000000000)
  directionHi := (345501243984748639787/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree143.table
  base := (-4009706800822556231201311116548961491689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-48891131136319171606313681208690000000000000)
      constant := (990387121427714863183660571209942171839486359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree143.table
  base := (-125303339364594241940356132174131025913/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-25119269344738488829570782008265000000000000)
      constant := (523319637551621969440405618180728983330420848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172750621992374319893/50000000000000000000)
  centralHi := (345501243984748639787/100000000000000000000)
  directionLo := (346715663349487381303/100000000000000000000)
  directionHi := (43339457918685922663/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree144.table
  base := (-3893299638761259034967552210998092311361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5471084562517855760417628653250000000000000)
      constant := (111695249849097956596138355971509841290689799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree144.table
  base := (-1946649845485461907109162623139277964263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2810921724792231715332052525665000000000000)
      constant := (59017032916494552697410592161355578417760017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346715663349487381303/100000000000000000000)
  centralHi := (43339457918685922663/12500000000000000000)
  directionLo := (21745365241523785611/6250000000000000000)
  directionHi := (347925843864380569777/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree145.table
  base := (-3775009402734785980876029148277090342651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-49588390989002232081203634549810000000000000)
      constant := (1020237225231176746612266223937763228430018181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree145.table
  base := (-151000377962222155662132011532283430337/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-50954643403043364092812326907410000000000000)
      constant := (1078089367852276489589202080859559176624811175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21745365241523785611/6250000000000000000)
  centralHi := (347925843864380569777/100000000000000000000)
  directionLo := (349131829608254975821/100000000000000000000)
  directionHi := (174565914804127487911/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree146.table
  base := (-3654836131527407031221388629200100866231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-49937020915343762318648611220370000000000000)
      constant := (1035327051041665507444376179036934799661929161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree146.table
  base := (-1169547575238910409001402238002568133/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-51312695759826557309647708352850000000000000)
      constant := (1093987601015764527132788284554314397125384375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349131829608254975821/100000000000000000000)
  centralHi := (174565914804127487911/50000000000000000000)
  directionLo := (35033366390124978253/10000000000000000000)
  directionHi := (350333663901249782531/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree147.table
  base := (-88319496581631972017024281243993001229/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-798184933995004643747517268110000000000000)
      constant := (16675027395587701205403185781200137636902920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree147.table
  base := (-3532779899720953991085052422786721630097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (968)
      previous := (418)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-820170605025551595658461742830000000000000)
      constant := (17619068124386318146434549757014436537303889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35033366390124978253/10000000000000000000)
  centralHi := (350333663901249782531/100000000000000000000)
  directionLo := (43941423665371711853/12500000000000000000)
  directionHi := (14061255572918947793/4000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree148.table
  base := (-3408840635433962501010865422386358356669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-50634280768026822793538564561490000000000000)
      constant := (1065836249723475560603439884564848543682380739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree148.table
  base := (-3408840667773235469380832564707299656941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-52028800473392943743318471243730000000000000)
      constant := (1126130440165478626856482823465756727661601171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43941423665371711853/12500000000000000000)
  centralHi := (14061255572918947793/4000000000000000000)
  directionLo := (352725047730107144741/100000000000000000000)
  directionHi := (176362523865053572371/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree149.table
  base := (-3283018484895149739136989672253795039893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-50982910694368353030983541232050000000000000)
      constant := (1081255622299712606493044749458239687486664683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree149.table
  base := (-1641509256790773051193651568057954133637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-26193426415088068480076926344585000000000000)
      constant := (571187522928557373887222508005842980043594747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352725047730107144741/100000000000000000000)
  centralHi := (176362523865053572371/50000000000000000000)
  directionLo := (176957340136735090049/50000000000000000000)
  directionHi := (353914680273470180099/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree150.table
  base := (-3155313447902657892599040028015991970701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5703504513412209252047613100290000000000000)
      constant := (121864982611871656972808916150894947540920859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree150.table
  base := (-3155313473347668625810882915198967723947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5860545020773258908554359348290000000000000)
      constant := (128748345418617947811249381799897255233739373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176957340136735090049/50000000000000000000)
  centralHi := (353914680273470180099/100000000000000000000)
  directionLo := (355100327414575727317/100000000000000000000)
  directionHi := (177550163707287863659/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree151.table
  base := (-3025725560117745358017854062019631550347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-51680170547051413505873494573170000000000000)
      constant := (1112423913203332944813958267939649082376672757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree151.table
  base := (-3025725582686647984224067990918720609931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-53102957543742523393824615580050000000000000)
      constant := (1175210628755462861051872847050833597899183861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355100327414575727317/100000000000000000000)
  centralHi := (177550163707287863659/50000000000000000000)
  directionLo := (178141014470843533659/50000000000000000000)
  directionHi := (356282028941687067319/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree152.table
  base := (-2894254856623796264139867588454299938849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-52028800473392943743318471243730000000000000)
      constant := (1128172831249930751062084213456504883542708319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree152.table
  base := (-1447127438320413652880181041732100259367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-26730504950262858305329998512745000000000000)
      constant := (595900802840867840075384186150765294070572377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178141014470843533659/50000000000000000000)
  centralHi := (356282028941687067319/100000000000000000000)
  directionLo := (357459823985397553753/100000000000000000000)
  directionHi := (178729911992698776877/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree153.table
  base := (-1380450685970208693520834862537338627233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5819714488859385997862605323810000000000000)
      constant := (127114621945514445800601122188917067330780494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree153.table
  base := (-690225347423342029344619099769910270611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-2989947903183828323749743248385000000000000)
      constant := (67139335522750906638746215954087939141321098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357459823985397553753/100000000000000000000)
  centralHi := (178729911992698776877/50000000000000000000)
  directionLo := (3586337510337498331/1000000000000000000)
  directionHi := (358633751033749833101/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree154.table
  base := (-2625665140036986535888357314894767328629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-7532294332296572031172632083550000000000000)
      constant := (165714315978229466817051379614424666924667357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree154.table
  base := (-2625665155781286047504443278591185775953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8712)
      previous := (3762)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-7739587802013157577761537130910000000000000)
      constant := (175047132829158394866091495615178797665034649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3586337510337498331/1000000000000000000)
  centralHi := (358633751033749833101/100000000000000000000)
  directionLo := (35980384794691109403/10000000000000000000)
  directionHi := (359803847946911094031/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree155.table
  base := (-2488546194345687935466391410433467750237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-53074690252417534455653401255410000000000000)
      constant := (1176078674131167178415755422341214566499309347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree155.table
  base := (-31106827603850380898793145327420488267/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-27267583485437648130583070680905000000000000)
      constant := (621133638366467361636991041969393723282731080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35980384794691109403/10000000000000000000)
  centralHi := (359803847946911094031/100000000000000000000)
  directionLo := (72194030394284035403/20000000000000000000)
  directionHi := (45121268996427522127/12500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree156.table
  base := (-1174772283887033432705258192547867652047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-5935924464306562743677597547330000000000000)
      constant := (132474109358855855231080788266992780730894546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree156.table
  base := (-2349544580155634068646612036906852174271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-6099246591962054386444613645250000000000000)
      constant := (139924453340609489936910277013284078191146489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72194030394284035403/20000000000000000000)
  centralHi := (45121268996427522127/12500000000000000000)
  directionLo := (362132699754021712287/100000000000000000000)
  directionHi := (11316646867313178509/3125000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree157.table
  base := (-110433014635856645030911193395374261089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-53771950105100594930543354596530000000000000)
      constant := (1208565142014637030708506529210530191154755180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree157.table
  base := (-2208660303696456024275354317175378796523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-55251271684441682694836904252690000000000000)
      constant := (1276488339673274928925888761946780921556600213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362132699754021712287/100000000000000000000)
  centralHi := (11316646867313178509/3125000000000000000)
  directionLo := (1419107528730866497/390625000000000000)
  directionHi := (363291527355101823233/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree158.table
  base := (-82635736042761539713485866934526620683/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-54120580031442125167988331267090000000000000)
      constant := (1224973147359382288221107372123271596062729325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree158.table
  base := (-2065893410804540644925425615282910433039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-55609324041224875911672285698130000000000000)
      constant := (1293772055429795199904018109988922128491268209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1419107528730866497/390625000000000000)
  centralHi := (363291527355101823233/100000000000000000000)
  directionLo := (182223335130869665701/50000000000000000000)
  directionHi := (364446670261739331403/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree159.table
  base := (-480310981058589326138379058088347928523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-6052134439753739489492589770850000000000000)
      constant := (137943444459921524083457974510217154254085428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree159.table
  base := (-384248786573322269232180056890353880887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6776)
      previous := (2926)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-6218597377556452125389740793730000000000000)
      constant := (145685691912274701903356302904226769692644165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182223335130869665701/50000000000000000000)
  centralHi := (364446670261739331403/100000000000000000000)
  directionLo := (182799081700192913439/50000000000000000000)
  directionHi := (365598163400385826879/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree160.table
  base := (-110919493321186538874546618368829216851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-54817839884125185642878284608210000000000000)
      constant := (1258118700231626437907521059034305869413094096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree160.table
  base := (-1774711900792718399773558431296898773827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-56325428754791262345343048589010000000000000)
      constant := (1328685854892624291075713035150982608766680637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182799081700192913439/50000000000000000000)
  centralHi := (365598163400385826879/100000000000000000000)
  directionLo := (183373020574593711119/50000000000000000000)
  directionHi := (366746041149187422239/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree161.table
  base := (-406574334560170076666702789734033204867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8811)
      previous := (3663)
      next := (0)
      square := (84801873974966814513642973920000000000000)
      linear := (-7880924258638102268617608754110000000000000)
      constant := (182122321073641943257137743812448212691361644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree161.table
  base := (-813148672513278691869623710335353145991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (4356)
      previous := (1881)
      next := (0)
      square := (42400936987483407256821486960000000000000)
      linear := (-4048820079398175397298459288175000000000000)
      constant := (96165424168244292427967921345474854766223103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183373020574593711119/50000000000000000000)
  centralHi := (366746041149187422239/100000000000000000000)
  directionLo := (9197258433749012211/2500000000000000000)
  directionHi := (367890337349960488441/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree162.table
  base := (-73800014476963653505055993625029853671/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-6168344415200916235307581994370000000000000)
      constant := (143522626874647321252489652201497236690621780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree162.table
  base := (-23062504618054281161530477861120906757/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-3168974081575424932167433971105000000000000)
      constant := (75781193193324441711621392408673861763845216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9197258433749012211/2500000000000000000)
  centralHi := (367890337349960488441/100000000000000000000)
  directionLo := (23064442832489573447/6250000000000000000)
  directionHi := (369031085319833175153/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree163.table
  base := (-1323820776586543352611916877563195024573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-55863729663149776355213214619890000000000000)
      constant := (1308660883183332286757233872631576678947469763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree163.table
  base := (-264764156384033944158390387368729682209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-57399585825140841995849192925330000000000000)
      constant := (1381922472148636817317892283441097559456562395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23064442832489573447/6250000000000000000)
  centralHi := (369031085319833175153/100000000000000000000)
  directionLo := (185084158931282022619/50000000000000000000)
  directionHi := (370168317862564045239/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree164.table
  base := (-1169758828495800735157178467954460006219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-56212359589491306592658191290450000000000000)
      constant := (1325727971334462063527623007231228748235316789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree164.table
  base := (-29243970830603045953959267130699508509/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-28878819090962017606342287185385000000000000)
      constant := (699949461123149496106485426486705073014555580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185084158931282022619/50000000000000000000)
  centralHi := (370168317862564045239/100000000000000000000)
  directionLo := (371302067279548701973/100000000000000000000)
  directionHi := (185651033639774350987/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree165.table
  base := (-2027628947902341193099306685228349597/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6853)
      previous := (2849)
      next := (0)
      square := (65957013091640855732833424160000000000000)
      linear := (-6284554390648092981122574217890000000000000)
      constant := (149211656245707547550562941558482148913861500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree165.table
  base := (-253453619535682557739357623929738727511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (3388)
      previous := (1463)
      next := (0)
      square := (32978506545820427866416712080000000000000)
      linear := (-3228649474372623801639997545345000000000000)
      constant := (78777268203278545186264444678718970442335298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371302067279548701973/100000000000000000000)
  centralHi := (185651033639774350987/50000000000000000000)
  directionLo := (372432365380524857023/100000000000000000000)
  directionHi := (5819255709070700891/1562500000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree166.table
  base := (-427993870608301815864944562821760067599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-56909619442174367067548144631570000000000000)
      constant := (1360191687701870259731345239496850868583399138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree166.table
  base := (-855987744932202706838277738515156283289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-58473742895490421646355337261650000000000000)
      constant := (1436198188274632391948700275228373344711625959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372432365380524857023/100000000000000000000)
  centralHi := (5819255709070700891/1562500000000000000)
  directionLo := (5836863179593529317/1562500000000000000)
  directionHi := (373559243493985876289/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree167.table
  base := (-174069664536155214267613299391186174669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-57258249368515897304993121302130000000000000)
      constant := (1377588315695422402942476583709470528290954956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree167.table
  base := (-348139330719094843242300275081455530533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (30492)
      previous := (13167)
      next := (0)
      square := (296806558912383850797750408720000000000000)
      linear := (-29415897626136807431595359353545000000000000)
      constant := (727260501991317670740549053896876702999314523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5836863179593529317/1562500000000000000)
  centralHi := (373559243493985876289/100000000000000000000)
  directionLo := (374682732477312448211/100000000000000000000)
  directionHi := (93670683119328112053/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree168.table
  base := (-534687252184805834271751796582049901033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (979)
      previous := (407)
      next := (0)
      square := (9422430441662979390404774880000000000000)
      linear := (-914394909442181389562509491630000000000000)
      constant := (22144361747350427943366215782615330856234921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree168.table
  base := (-267343627552089227161231156755197115477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (484)
      previous := (209)
      next := (0)
      square := (4711215220831489695202387440000000000000)
      linear := (-469760695309974667301794445655000000000000)
      constant := (11690152973603963975540209971004422581724949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell006.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374682732477312448211/100000000000000000000)
  centralHi := (93670683119328112053/25000000000000000000)
  directionLo := (375802862726631644357/100000000000000000000)
  directionHi := (187901431363315822179/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree169.table
  base := (-185606775196027517376630067047222781037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (61677)
      previous := (25641)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-57955509221198957779883074643250000000000000)
      constant := (1412711110757453048105066374168694145564128294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 19
  qDenominator := 63
  table := BinomialMassData.Q19_63.Degree169.table
  base := (-371213552979656516461495404976208574613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (60984)
      previous := (26334)
      next := (0)
      square := (593613117824767701595500817440000000000000)
      linear := (-59547899965840001296861481597970000000000000)
      constant := (1491513000241665334347856189984779428167361003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_63.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell006.Kernel169
