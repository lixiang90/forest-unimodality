import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell117.Parameters
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch000_049
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch050_099
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch100_149
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch150_199
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch000_049
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch050_099
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch100_149
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel000
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
  base := (364667785391281939705265811/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (705845518121273191036735280000000000000)
      linear := (-41316297703533587382107584000000000000)
      constant := (729335570782563879410531622000000000000000) }

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
  base := (364667785391281939705265811/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (705845518121273191036735280000000000000)
      linear := (-41316297703533587382107584000000000000)
      constant := (729335570782563879410531622000000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel001
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
  base := (201555362967095204013180693090051653502529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-15009311137003952074714628535431424000000000000)
      constant := (7769381766685378880990178478059323639999980877618) }

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
  base := (201378243255550522819991862253215244297699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-1669422324099902601654658854572336000000000000)
      constant := (862507388085584174771089526613187714444443421862) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel002
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
  base := (47359107847478584929748585667694364915063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-29222733168813173821406169023736384000000000000)
      constant := (4577158326372083543565045729317923214249981521115) }

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
  base := (47287145259997738484960350773237964536333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-3250412525400390722417863481686176000000000000)
      constant := (507806715864841708063014738002812076583332634385) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel003
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
  base := (1194212101254906607391636657032728654049/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-4826239466735821729788634390226816000000000000)
      constant := (323359949519539319001227351726031877567275510125) }

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
  base := (4656072200712315319155149859023196593759/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-4831402726700878843181068108800016000000000000)
      constant := (322764184179992972967286338476160756645995426272) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel004
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
  base := (101093187527907791177794595533117888220763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-57649577232431617314789250000346304000000000000)
      constant := (2008485942531461428964595018807040267638676533923) }

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
  base := (50444084862047335991720024252204532198863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-6412392928001366963944272735913856000000000000)
      constant := (222740893276915325131663373068600148755896400894) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel005
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
  base := (72950750629918156829627866059193906441229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-71862999264240839061480790488651264000000000000)
      constant := (1500215336235287347151408925977247941021361861509) }

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
  base := (72803399722543901924650392550389636240623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-7993383129301855084707477363027696000000000000)
      constant := (166397960734773561047656332246323295330706009887) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel006
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
  base := (11066227034538191210403985001465427818427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-9564046810672228978685814552995136000000000000)
      constant := (133564238989800287640196234445834597371493897815) }

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
  base := (11044566583577871802779162908243471054859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-9574373330602343205470681990141536000000000000)
      constant := (133365136268219906583329811701603025491087514855) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel007
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
  base := (43478724460415161617324108246816914935843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-2046731496486924133772732070719616000000000000)
      constant := (20866641134404897570811608269060358951813022747) }

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
  base := (2712254423153871073794171012928206074431/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-227660480242914925025181359535824000000000000)
      constant := (2315812532761251772402834911472859512595528176) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel008
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
  base := (34967470511381650381774923083046685550123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-114503265359668504301555411953566144000000000000)
      constant := (914643389235134556028533176992033033738080938483) }

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
  base := (349018309400210596720089664012584241539/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-12736353733203319446997091244369216000000000000)
      constant := (101544556584719468816482975698980980047858789100) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel009
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
  base := (5704264217208265174147703840894522023657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-14301854154608636227582994715763456000000000000)
      constant := (94892340883653685920802112157724300046263547165) }

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
  base := (14233704076745097832884672263820242653973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-14317343934503807567760295871483056000000000000)
      constant := (94850304793844761290537712898627141898083072074) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel010
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
  base := (11719955073674987647654132800568749051531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-142930109423286947794938492930176064000000000000)
      constant := (827137075950005270600812630293055031096174388902) }

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
  base := (23394535907106075908675581992399067135403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-15898334135804295688523500498596896000000000000)
      constant := (91897510754283929421460352436316958925535383707) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel011
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
  base := (19317278326930277665229165781526360483009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-1298706871529720409434958953871744000000000000)
      constant := (6827613947111498054661108845807562115255515809) }

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
  base := (19278491975774659581387293601600420268493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-144457225926485816605675248972816000000000000)
      constant := (758842310428385670700827548718145834129372677) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel012
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
  base := (15902836595402599206299707277915632843107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-19039661498545043476480174878531776000000000000)
      constant := (94024058443591426563542041801915277152768086483) }

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
  base := (15869390124343284872521738916478026003567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-19060314538405271930049909752824576000000000000)
      constant := (94082682465249503881989591004180948039228696223) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel013
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
  base := (3257908795120418668291691045103505206133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-185570375518714613035013114395090944000000000000)
      constant := (884185310713092025983084225160969388043644590772) }

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
  base := (13002673340733407491833035787394002643361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-20641304739705760050813114379938416000000000000)
      constant := (98333586737142900839059436733434582043767940209) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel014
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
  base := (5294302744945273945109747601416595165961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-4077220358173955811871523569048896000000000000)
      constant := (19139408949647953012936483885673713281998163938) }

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
  base := (5281747005585330910218547783635410235481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-453516223285841799419924877694944000000000000)
      constant := (2129118696025882282871109237738772708992091122) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel015
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
  base := (106120224270875048926722152738158291287/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-23777468842481450725377355041300096000000000000)
      constant := (111725899367602187518124044230419769901093192240) }

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
  base := (8467851652725107604500625808311886267333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-23803285142306736292339523634166096000000000000)
      constant := (111882578539977223655707428428278843698125265877) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel016
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
  base := (3335495568704333924924731672902945635789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-228210641614142278275087735860005824000000000000)
      constant := (1086064762820774791415654493566569271255505190538) }

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
  base := (6652146117067058446801469697697784728467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-25384275343607224413102728261279936000000000000)
      constant := (120864746255389613679792673515374045801484184323) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel017
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
  base := (508334810222964726040095716889060903293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-242424063645951500021779276348310784000000000000)
      constant := (1178474879552752494395992318095343783686830160530) }

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
  base := (633382139751711000609288583686898933381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-26965265544907712533865932888393776000000000000)
      constant := (131167755639888552097143936476837325465134060712) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel018
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
  base := (230486559691154775764288628098190203029/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-28515276186417857974274535204068416000000000000)
      constant := (142446002950563282030554787158232692266671643216) }

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
  base := (918431182740031310030746653120248943209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-28546255746208200654629137515507616000000000000)
      constant := (142708432115507435687752201253046184441309216484) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel019
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
  base := (2453327069894098877794821082479023176901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (7790706)
      previous := (3895353)
      next := (3895353)
      square := (37664622692469258746911231276080000000000000)
      linear := (-750279522741190979266377721121664000000000000)
      constant := (3867272935357929713988604665992019155742614261) }

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
  base := (1220605651314651232353376078144799936383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-83454974923846783311336127818896000000000000)
      constant := (430527860632241773855017857823165037645629614) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel020
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
  base := (1355143759162541805323963436504993629917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-285064329741379165261853897813225664000000000000)
      constant := (1520211067374793609531633060788245690396046374357) }

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
  base := (672359393198078554748080580371327434239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-31708236148809176896155546769735296000000000000)
      constant := (169251055387827247572846653515317115458189388382) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel021
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
  base := (186619397905602431008985011548496578673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-678634357762331943330035007486464000000000000)
      constant := (3750579242508638010260401961239443758106030626) }

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
  base := (364280415650783302022403273279292980243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-679371966328768673814668395854064000000000000)
      constant := (3758309978897739993856278094510396796669994483) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel022
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
  base := (-508541527139300696223798254007864474623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-2590836147148740568225098998263104000000000000)
      constant := (14852541250709718842711582062493421967775543777) }

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
  base := (-516230764045575427340760727943305400433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-288183607862893827584148396892256000000000000)
      constant := (1653755709003142066064933239704322870771740663) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel023
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
  base := (-1303276670252336557040491956906836626243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-327704595836806830501928519278140544000000000000)
      constant := (1949415249696154584833330865308563870974124066997) }

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
  base := (-40933436550527700601761149705644834557/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-36451206752710641258445160651076816000000000000)
      constant := (217064867876407703404576959450400545475330190944) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel024
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
  base := (-404315144021928428221191932778861720461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-37990890874290672472068895529605056000000000000)
      constant := (234508261642978259769081243408677306591193049455) }

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
  base := (-405444887980458943568913625902779939897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-38032196954011129379208365278190656000000000000)
      constant := (235015809629264897892179266542089808014112990035) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel025
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
  base := (-1336028312972216347650881267899020356131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-356131439900425273995311600254750464000000000000)
      constant := (2280468796285384110070528644048141950588628457898) }

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
  base := (-334611570865538180956685228349620537919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-39613187155311617499971569905304496000000000000)
      constant := (253938862316216956185739978679562308310998783112) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel026
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
  base := (-3261728921722471354266275903015490866029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-370344861932234495742003140743055424000000000000)
      constant := (2458963547289051003007217982510775155475115377691) }

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
  base := (-3265866494116381892908085069341417161341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-41194177356612105620734774532418336000000000000)
      constant := (273819060170215339909065744262555276291797725171) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel027
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
  base := (-1898150326537792672256406816817288637671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-42728698218227079720966075692373376000000000000)
      constant := (293994294653612942338992614472362905471753518802) }

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
  base := (-189991944894199897353670702410263268753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-42775167557912593741497979159532176000000000000)
      constant := (294644218763154741310274697243850076354448202860) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel028
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
  base := (-4280425233287754864229008248137111320677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-8138198081548019168069106565707456000000000000)
      constant := (57986417752488685091558026608112953563613571667) }

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
  base := (-428344968245186562978933210744958254091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-905227709371695548209411914013184000000000000)
      constant := (6457232795670808525481679244032286785030510290) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel029
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
  base := (-235895020253689677636836562202670175167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-412985128027662160982077762207970304000000000000)
      constant := (3045047844120347401724011870171903803172637007860) }

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
  base := (-2360242386313515405400809975913643406493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-45937147960513569983024388413759856000000000000)
      constant := (339091521568266637262866594502499905951375968166) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel030
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
  base := (-5111828864329745743616146060340958479291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-47466505562163486969863255855141696000000000000)
      constant := (361892111822301232570661495757474563040638401621) }

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
  base := (-2557018283943348296128514311611403095823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-47518138161814058103787593040873696000000000000)
      constant := (362698943628369178126528892497836505534392842626) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel031
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
  base := (-5464748110788064435529244107299505184821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-441411972091280604475460843184580224000000000000)
      constant := (3477229076041152987491529567697790132483628749459) }

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
  base := (-1093326725669864982049253201972563296581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-49099128363114546224550797667987536000000000000)
      constant := (387221261116485048083900644591576009347301108055) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel032
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
  base := (-2889367774083763377902172774819082691193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-455625394123089826222152383672885184000000000000)
      constant := (3705608035346991687259556884089896314388010736094) }

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
  base := (-2890172809565491303513413364307485687413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-50680118564415034345314002295101376000000000000)
      constant := (412654044185559436263886019288108014333435049206) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel033
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
  base := (-3027746823299210275266343385999304889447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-431440602529751191890582115850496000000000000)
      constant := (3619956922947304449805676151725764591621144034) }

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
  base := (-6056868328289178790299188298846707966537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-431909989799301838562621544811696000000000000)
      constant := (3628046803499202313678886390246128582779927007) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel034
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
  base := (-1574104755831410275593371213932157809823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-484052238186708269715535464649495104000000000000)
      constant := (4186777333782719009786752670869488463546890391268) }

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
  base := (-1259518523121331931795279389193359117199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-53842098967016010586840411549329056000000000000)
      constant := (466237141276854842458657028550164699698399467845) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel035
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
  base := (-6502658536976457833980569276682474315401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-10168686943235050846167898064036736000000000000)
      constant := (90602421982049517731889908570156055554860720271) }

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
  base := (-130073207757797500472146278375810908337/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-1131083452414622422604155432172304000000000000)
      constant := (10089429270285389991834014075040650185646575150) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel036
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
  base := (-3337577441851084113414762787317202130747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-56942120250036301467657616180678336000000000000)
      constant := (522259884404907635012642679835355830785230348714) }

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
  base := (-417250630555024926612165300262795478317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-57004079369616986828366820803556736000000000000)
      constant := (523426333508898572502959995245963787277921936432) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel037
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
  base := (-212958865562801352635010690662357926649/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-526692504282135934955610086114409984000000000000)
      constant := (4969223240057461515696202399597811540546107477472) }

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
  base := (-681541370599286359503072448409245108459/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-58585069570917474949130025430670576000000000000)
      constant := (553368386733667561555419965938279216564527186290) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel038
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
  base := (-3460941886042562833457960057717463960817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (7790706)
      previous := (3895353)
      next := (3895353)
      square := (37664622692469258746911231276080000000000000)
      linear := (-1498354366520623702776458799453504000000000000)
      constant := (14532296989200467829522076143024148811173688126) }

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
  base := (-6922506906843713018173020761479449591731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-166664985518609315983083739772256000000000000)
      constant := (1618301477437757719666623740304276343370626901) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel039
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
  base := (-3498640847637711226575804941243267595711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-61679927593972708716554796343446656000000000000)
      constant := (614570748324029789146520746735023921158871285282) }

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
  base := (-6997813606275145249692407727364920696713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-61747049973518451190656434684898256000000000000)
      constant := (615940552001900617413966937873379556053297092903) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel040
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
  base := (-1760327991162697115382431365423889646129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-569332770377563600195684707579324864000000000000)
      constant := (5824147435645621285159247283580323010712162662364) }

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
  base := (-1760441503448510822197273550861067084223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-63328040174818939311419639312012096000000000000)
      constant := (648568617586447765740252117053403234824034806852) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel041
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
  base := (-7054333415947643310056041051315172715091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-583546192409372821942376248067629824000000000000)
      constant := (6125184402921451512486808568292572339818760522789) }

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
  base := (-1763680252432251713370604843805286521651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-64909030376119427432182843939125936000000000000)
      constant := (682090266253079937128649372796777526771761483124) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel042
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
  base := (-7036642661903386502885159830128346214829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-1355463978324675836029632173596224000000000000)
      constant := (14590117739223096528225849478665411708990054451) }

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
  base := (-3518486768083166523857258882615635827497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-1356939195457549296998898950331424000000000000)
      constant := (14622548300344873998634513930155860822838207086) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel043
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
  base := (-1747121273563600031235541298571594705277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-611973036472991265435759329044239744000000000000)
      constant := (6751315268813634779061059296565113030841395020332) }

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
  base := (-873595944756076149897105623593004132287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-68071010778720403673709253193353616000000000000)
      constant := (751811896802904231457593913232183670707048048776) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel044
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
  base := (-3455031950122476626754222128155389466089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-5175094698386780885805379087045824000000000000)
      constant := (58482648977761071753563160582147163683218330222) }

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
  base := (-3455152522235433266330989970044788659203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-575636371735709849541094692731136000000000000)
      constant := (6512486977047158601773384276569739466814716266) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel045
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
  base := (-1700386864852336273837197472878941567963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-71155542281845523214349156668983296000000000000)
      constant := (823277161326081249130877049451093010860482406612) }

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
  base := (-3400876667601260323935497898617034710793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-71232991181321379915235662447581296000000000000)
      constant := (825101590807449779706331348979051332066189394766) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel046
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
  base := (-3331537708827931716588462465922631309957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-654613302568418930675833950509154624000000000000)
      constant := (7750594355646601774932519646408439087823295625606) }

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
  base := (-6663251188807765461377275893005629032167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-72813981382621868035998867074695136000000000000)
      constant := (863083599562605712963827211863820250794049750377) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel047
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
  base := (-1298952736021014616646969555219168500707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-668826724600228152422525490997459584000000000000)
      constant := (8099698004727158296688445405648108347088961660265) }

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
  base := (-324745687661796938982849820797689033767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-74394971583922356156762071701808976000000000000)
      constant := (901956704029072814375557479366735674409703199540) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel048
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
  base := (-393544282447219809494732381071621383693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-75893349625781930463246336831751616000000000000)
      constant := (939644838294476026167505148421770284969702356528) }

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
  base := (-3148418327421942021419633521364523413627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-75975961785222844277525276328922816000000000000)
      constant := (941720699531161313304416449138294800771397183274) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel049
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
  base := (-6068989957811881025205664328775522966321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-14229664666609114202365481060695296000000000000)
      constant := (180038968038921488586481023332342471431773191591) }

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
  base := (-3034549682719189629474691647204389336257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-1582794938500476171393642468490544000000000000)
      constant := (20048477876936318532900918927129486138805915966) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel050
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
  base := (-5811674558763457872475553280408983315039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-711466990695655817662600112462374464000000000000)
      constant := (9195014390279313946351811052716465943118759615481) }

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
  base := (-581176797743736576454659258215097519249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-79137942187823820519051685583150496000000000000)
      constant := (1023920711883065202118153234417712899378225371190) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel051
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
  base := (-5524817725717685506955297779068557903209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-80631156969718337712143516994519936000000000000)
      constant := (1064013038500818475979313222944671145789266455879) }

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
  base := (-5524897493317354880303842454811599958399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-80718932389124308639814890210264336000000000000)
      constant := (1066356469545122447263523634031201746608641490769) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel052
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
  base := (-5208465604007489111611642510151853780741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-739893834759274261155983193438984384000000000000)
      constant := (9965217413678949163455121869441646089876522499139) }

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
  base := (-5208533716074123859820770386550055532231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-82299922590424796760578094837378176000000000000)
      constant := (1109682590920739074783746423808882276190534266761) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel053
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
  base := (-4862656651643002880774390450265577947673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-754107256791083482902674733927289344000000000000)
      constant := (10362313850965068349037268266930152788743453797967) }

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
  base := (-4862714811615916101683511103391054264731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-83880912791725284881341299464492016000000000000)
      constant := (1153898994320788223664033197153347700574451974261) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel054
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
  base := (-897484587815158611081943676542304813281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-85368964313654744961040697157288256000000000000)
      constant := (1196378448953591189456418153938674501945512796555) }

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
  base := (-897494520228218608140366932490253425909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-85461902993025773002104504091605856000000000000)
      constant := (1199005611636163378238521601337217267825202897895) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel055
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
  base := (-4082791225428736596184595202325912297259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-6467223974005801044595519131437184000000000000)
      constant := (92400772455050682432477479579150032436364069941) }

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
  base := (-15948568871358723455991667001641182209/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-719362753672117860519567840650576000000000000)
      constant := (10289275917749867835948086510234020096743679744) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel056
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
  base := (-18243919251833465042745070694924550023/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-16260153528296145880464272559024576000000000000)
      constant := (236766851021742219094488137322091257314801606600) }

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
  base := (-3648820059531987485617334009569254853599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-1808650681543403045788385986649664000000000000)
      constant := (26365087145488021231839019861916229378739942081) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel057
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
  base := (-3185419473778071910972393417206054687641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-249603245588895158476282208642816000000000000)
      constant := (3702878541133766983794438458794057301756976511) }

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
  base := (-79636259787177014422801093094556431533/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-249874996113371848654831351725616000000000000)
      constant := (3710986770837317463088288661093386996697633720) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel058
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
  base := (-2692713689711045793841213443761507439871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-825174366950129591636132436368814144000000000000)
      constant := (12467723206902697522338726314459552906741876728409) }

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
  base := (-134637004436691746867304519134980917931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-91785863798227725485157322600061216000000000000)
      constant := (1388333215383850749065733775130352288553378869220) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel059
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
  base := (-1085339768161147815432023961906036215417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-839387788981938813382823976857119104000000000000)
      constant := (12912787929184437117710565198560781881089594360286) }

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
  base := (-86828083061507863456665816967036143133/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-93366853999528213605920527227175056000000000000)
      constant := (1437890215798812997601391537327544649433964098075) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel060
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
  base := (-1619327919757844842097941916626633924001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-94844579001527559458835057482824896000000000000)
      constant := (1485094037433359554938841167515268728174719903631) }

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
  base := (-809673582334531059557517520443788987283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-94947844200828701726683731854288896000000000000)
      constant := (1488337202380260895792220503394597055618156145146) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel061
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
  base := (-1038667966738262096769459997412187986171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-867814633045557256876207057833729024000000000000)
      constant := (13826898254239146160977888106550021917510044466109) }

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
  base := (-129835549695761800189328811510260962749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-96528834402129189847446936481402736000000000000)
      constant := (1539674155769759377422726077762725310027375084952) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel062
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
  base := (-214353659018643881105955348013312322731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-882028055077366478622898598322033984000000000000)
      constant := (14295943534014490368228918559095901352907954300698) }

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
  base := (-4287213457474486185239323689846177203/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-98109824603429677968210141108516576000000000000)
      constant := (1591901059763604999013440837929989354754619209300) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel063
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
  base := (105273813539715717837743559971648578077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2032293598887019728729229339705984000000000000)
      constant := (33498825516905125394669084350520355163077962874) }

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
  base := (42107130302206420349607288843782443297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2034506424586329920183129504808784000000000000)
      constant := (33571793893743025785389738830505858304528281285) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel064
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
  base := (175818301426851786170869414594232260351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-910454899140984922116281679298643904000000000000)
      constant := (15258013707781291205945395889888429199898484428355) }

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
  base := (27471290123726916584615497013749939539/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-101271805006030654209736550362744256000000000000)
      constant := (1699024667493274503595612759733873118218916796512) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel065
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
  base := (1576919828551742958120504843822857015097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-924668321172794143862973219786948864000000000000)
      constant := (15751038411931696723844763185204605921818915357137) }

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
  base := (1576911101769319246867421448888871128649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-102852795207331142330499754989858096000000000000)
      constant := (1753921350338929984427589863549413764208755331481) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel066
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
  base := (2304028823906593938752909718479054996323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-862150361069424578153962130647616000000000000)
      constant := (14923834795990132374723884035965632003829957547) }

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
  base := (2304021374877435811322376931715335232467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-863089135608525871498040988570016000000000000)
      constant := (14956263978071585492277915776072328564927108763) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel067
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
  base := (3060415333581466025555527567958941550443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-953095165236412587356356300763558784000000000000)
      constant := (16761066689621240332411481324420818373906421201203) }

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
  base := (3060408975575292967452364409025751505681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-106014775609932118572026164244085776000000000000)
      constant := (1866384433822020158999196479346913410724462936289) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel068
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
  base := (961519176729154743476946795291414555723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-967308587268221809103047841251863744000000000000)
      constant := (17278070151235145814747533426524623740523858144332) }

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
  base := (3846071280456360764931059344476451298413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-107595765811232606692789368871199616000000000000)
      constant := (1923950822149946916625045869954369365589132934397) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel069
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
  base := (2330505359799778201271057342472680954749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-109058001033336781205526597971129856000000000000)
      constant := (1978118492758591664553196706563134843324870324762) }

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
  base := (4661006088485505171517810201217158145891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-109176756012533094813552573498313456000000000000)
      constant := (1982407101619414748649723089637842931563562573779) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel070
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
  base := (2752607752296759219691328933429547551083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-20321131251670209236661855555683136000000000000)
      constant := (374205214376172436875295429480302369198419417414) }

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
  base := (5505211552507909007244427420804274157103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2260362167629256794577873022967904000000000000)
      constant := (41668434046465933595521567438373831499456416143) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel071
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
  base := (6378689494359579164896034138854926783307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1009948853363649474343122462716778624000000000000)
      constant := (18877037329854513582496458763914976131058340182547) }

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
  base := (1275737224393336715855541068867581664233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-112338736415134071055078982752541136000000000000)
      constant := (2101989318803431011922956298918859900495463609885) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel072
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
  base := (7281431372504730811686591369205528309887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-113795808377273188454423778133898176000000000000)
      constant := (2158445765081712937446764748465655099423104528303) }

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
  base := (910178561871752535398518896296623559909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-113919726616434559175842187379654976000000000000)
      constant := (2163115250412695238862067423875533214978390931368) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel073
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
  base := (8213440033301408791808094576147800692109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1038375697427267917836505543693388544000000000000)
      constant := (19982979150775172955256906906167443660176117833989) }

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
  base := (4106718789095982083830050478590483872899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-115500716817735047296605392006768816000000000000)
      constant := (2225131060764476761696697623035044098753105919462) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel074
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
  base := (2293678636945916256650928329334738905877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1052589119459077139583197084181693504000000000000)
      constant := (20547939107078813881296031500191198303980389750068) }

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
  base := (1834942490647415656319433126006073719891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-117081707019035535417368596633882656000000000000)
      constant := (2288036747893096141863265669209898614008846898895) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel075
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
  base := (254131353383521905849014802461685429093/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-118533615721209595703320958296666496000000000000)
      constant := (2346765748845465133649427002738735807207294212680) }

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
  base := (10165252348537612411194006334447250984957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-118662697220336023538131801260996496000000000000)
      constant := (2351832310147105123928399243081485228143421429133) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel076
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
  base := (11185058139909088899928555615448493934843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (7790706)
      previous := (3895353)
      next := (3895353)
      square := (37664622692469258746911231276080000000000000)
      linear := (-2994504054079489149796620956117184000000000000)
      constant := (60115892065729416584030585248340331084857157323) }

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
  base := (11185056615749868112573548609875530081657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-333085006708134381326578963678976000000000000)
      constant := (6693954975453764416613505857794288017854144353) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel077
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
  base := (611706300500456214104409594262490045123/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2293292088376016597678352924720000000000000)
      linear := (-184724133168241660452567331024896000000000000)
      constant := (3759617976861678695958007218845928603132092540) }

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
  base := (2446824941997700997596881882567754317967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (254810232041779621964261436080000000000000)
      linear := (-20547255460100691479112533397744000000000000)
      constant := (418636035537519302096255701464542796543930435) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel078
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
  base := (6656228641002283374654057383579869328497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-123271423065146002952218138459434816000000000000)
      constant := (2543078397547969989528099124211677450669531590786) }

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
  base := (13312456173248707697614837086224767962767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-123405667824237487900421415142338016000000000000)
      constant := (2548558234856234778518015021957512428379699641023) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel079
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
  base := (1802506445757000806692579006779919735229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1123656229618123248316654786623218304000000000000)
      constant := (23492628807575228448735139308462155217711609884072) }

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
  base := (7210025310250338674652371993904225987343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-124986658025537976021184619769451856000000000000)
      constant := (2615913285777551617940406723959750912544606699134) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel080
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
  base := (15556908534333930374473692963465258211711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1137869651649932470063346327111523264000000000000)
      constant := (24105544667428303474697815817807004061280074952231) }

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
  base := (15556907728022334174565354758295603776847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-126567648226838464141947824396565696000000000000)
      constant := (2684158206773017756243874608362992483160246236543) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel081
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
  base := (16723027911124371454274114520995073203473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-128009230409082410201115318622203136000000000000)
      constant := (2747383683575532036891383941984753719837444301537) }

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
  base := (836151361180366132711783011088331745747/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-128148638428138952262711029023679536000000000000)
      constant := (2753292997260011148472227545118383306606255212860) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel082
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
  base := (358368189290424968879199429708074084869/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1166296495713550913556729408088133184000000000000)
      constant := (25355354257362401735757838539505919297430639497450) }

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
  base := (17918408878344796994593074427502149234499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-129729628629439440383474233650793376000000000000)
      constant := (2823317656748578116524801316657168059654895390131) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel083
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
  base := (19143052999449259412004358186789015132559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1180509917745360135303420948576438144000000000000)
      constant := (25992247979218345525625042198680366629772341568439) }

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
  base := (598220390616156972662358452941199993141/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-131310618830739928504237438277907216000000000000)
      constant := (2894232184826659670446977778308366293219814688928) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel084
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
  base := (20396958351802887877153256363606176491571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2709123219449363621428826505815744000000000000)
      constant := (60401665112440821904251428161165817395328312851) }

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
  base := (2039695792580221196715613592649446438643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2712073653715110543367360059286144000000000000)
      constant := (60531358798932314948362637880316500698863648830) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel085
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
  base := (21680125383521918073675914681423485902019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1208936761808978578796804029553048064000000000000)
      constant := (27290013260807074284582819138160859585869566545099) }

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
  base := (21680125020404565387304243591800392312581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-134472599233340904745763847532134896000000000000)
      constant := (3038730845420140138338679040039126673893686682389) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel086
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
  base := (11496276989226488673958511208757312554537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1223150183840787800543495570041353024000000000000)
      constant := (27950884815642861297388876082133949909670752474754) }

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
  base := (5748138417240601637617972513647678507467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-136053589434641392866527052159248736000000000000)
      constant := (3112314977398825526367695639710999727997394541292) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel087
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
  base := (24334244038870978392842748484973246438013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-137484845096955224698909678947739776000000000000)
      constant := (3179972108579028196849403600545171174505283446797) }

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
  base := (24334243775109423734054161941988245322113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-137634579635941880987290256786362576000000000000)
      constant := (3186788976877480130301418899320135930651845679697) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel088
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
  base := (12852597741277355650184140312339309395921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-10343611800862861520965939264611264000000000000)
      constant := (242120708627507422709770825394268212790280038242) }

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
  base := (803287351805758295143339764478429233039/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1150541899481341893454987284408896000000000000)
      constant := (26959940856881014432273837775616093910503259872) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel089
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
  base := (27105408240327892065351322725174232951983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1265790449936215465783570191506267904000000000000)
      constant := (29981455114461729461723566784861650926282826115543) }

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
  base := (27105408048800637449775260351741636741027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-140796560038542857228816666040590256000000000000)
      constant := (3338406577668249543979159548421345579289755218963) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel090
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
  base := (222928767609306696144955725308865701563/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-142222652440891631947806859110508096000000000000)
      constant := (3408255231965570735204392754844171721316953183616) }

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
  base := (1426744104540210619700030408382912021287/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-142377550239843345349579870667704096000000000000)
      constant := (3415550178711661099035676153407996340401800698060) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel091
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
  base := (29993617474583258239802559350411784476347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-26412597836731304270958230050670976000000000000)
      constant := (640308809442254236610233643641099650419401819763) }

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
  base := (3749202166944315322824498840909840063913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-2937929396758037417762103577445264000000000000)
      constant := (71297625443052755303581992526955425790654270024) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel092
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
  base := (1574080693045846961235570698051047366997/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1308430716031643131023644812971182784000000000000)
      constant := (32083958838609294833837826531496865564333360340740) }

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
  base := (1259264549699197742115141480242536274489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-145539530642444321591106279921931776000000000000)
      constant := (3572506981575183029219115915687881200082293661025) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel093
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
  base := (32998871378348980392235890295737667557331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-146960459784828039196704039273276416000000000000)
      constant := (3644530957204366994373137894620643303772016995139) }

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
  base := (515607363710346950678570138803364490843/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-147120520843744809711869484549045616000000000000)
      constant := (3652320183235429468637232452740368328921673028288) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel094
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
  base := (138181559990975785718489446429703345037/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1336857560095261574517027893947792704000000000000)
      constant := (33525590990799236697558383592736386683555371969250) }

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
  base := (6909077982362769500466676205185555523709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-148701511045045297832632689176159456000000000000)
      constant := (3733023251628922580300421313465078875453627543105) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel095
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
  base := (3612116969460268501936872177029566939817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (7790706)
      previous := (3895353)
      next := (3895353)
      square := (37664622692469258746911231276080000000000000)
      linear := (-3742578897858921873306702034449024000000000000)
      constant := (94898603783981055521103371652275627214755749370) }

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
  base := (18060584810708952289501367846998749681237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-416295017302896913998326575632336000000000000)
      constant := (10566803841285438104636050159592731173720108346) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel096
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
  base := (9431552612082196309466001496441811467583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-151698267128764446445601219436044736000000000000)
      constant := (3888799282232924523440957475417376510276236632508) }

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
  base := (18863105193001997135837179055570644138583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-151863491447646274074159098430387136000000000000)
      constant := (3897098988417405098230154888112512984048509514254) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel097
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
  base := (19680256120805584339012071722800135714731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1379497826190689239757102515412707584000000000000)
      constant := (35747983712703246840897454799625185954232855363302) }

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
  base := (39360512188539138628663908163325440486059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-153444481648946762194922303057500976000000000000)
      constant := (3980471656732551549684574995598155761727705615771) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel098
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
  base := (20512037529952191089670549691407924253417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-28443086698418335949057021549000256000000000000)
      constant := (744995234358321340807826508822090179707643143586) }

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
  base := (41024075014715081724439449236051221227663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-3163785139800964292156847095604384000000000000)
      constant := (82953759012629746177751011518985025394445547503) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel099
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
  base := (1334903090343471774081061893607017652189/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1292860119609097964417342145444736000000000000)
      constant := (34223638064668935681626741826511889127986279072) }

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
  base := (42716898852516787129806446910731626480117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1294268281417749904433460432328336000000000000)
      constant := (34296583413641376246271982794792295740806789613) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel100
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
  base := (555487296557672291347405399886389537481/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1422138092286116904997177136877622464000000000000)
      constant := (38042309819105828537453982118941165215323042752080) }

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
  base := (4443898369185923488364138699944288997767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-158187452252848226557211916938842496000000000000)
      constant := (4235928861006212774862736081878068178978615560230) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel101
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
  base := (23095164776082303491423462123025416358869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1436351514317926126743868677365927424000000000000)
      constant := (38823070383436002955047677741799380396959089487898) }

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
  base := (2886895595267605505094841277262836005933/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-159768442454148714677975121565956336000000000000)
      constant := (4322860995467567210913886950661125660626924948432) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel102
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
  base := (23985468183212161884034323970872765625321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-161173881816637260943395579761581376000000000000)
      constant := (4401313727252880843887767365966464852977405366898) }

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
  base := (149909176070907254583995669757395842139/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-161349432655449202798738326193070176000000000000)
      constant := (4410682996419486430281812902132404457997826973120) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel103
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
  base := (49780804161342425062150267454189324352281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1464778358381544570237251758342537344000000000000)
      constant := (40408569304509049567880423548861466101771105985201) }

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
  base := (49780804141141551697392338585576527840291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-162930422856749690919501530820184016000000000000)
      constant := (4499394863849248971431669044040858355316995807379) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel104
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
  base := (51619932931852006840735378387384492441169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1478991780413353791983943298830842304000000000000)
      constant := (41213307661037763475021860271003312484316312062249) }

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
  base := (6452491614332453174457825082494860914603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-164511413058050179040264735447297856000000000000)
      constant := (4588996597746204886082831607559495767687423268056) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel105
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
  base := (13372080668428468456927125462659389481621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-3385952840011707514128423671925504000000000000)
      constant := (95297139716055347703012971331482019167786747604) }

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
  base := (53488322659083043682388726703326709866047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-3389640882843891166551590613763504000000000000)
      constant := (95499759144927490429398177320763034013658799007) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel106
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
  base := (27692986691692629456614063224116587149391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1507418624476972235477326379807452224000000000000)
      constant := (42846762165668738693835884514261417263366387575022) }

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
  base := (55385973370935261665555502727408283646439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-167673393460651155281791144701525536000000000000)
      constant := (4770869664907534317390728575965673916660044995991) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel107
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
  base := (57312885057909269532738335523147079943299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1521632046508781457224017920295757184000000000000)
      constant := (43675478313645794974809798897223347659160430435979) }

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
  base := (2865644252365791217871975083988844627571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-169254383661951643402554349328639376000000000000)
      constant := (4863140998158258701191866665467575999733390273980) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel108
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
  base := (59269057694821788046477837584494882588029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-170649496504510075441189940087118016000000000000)
      constant := (4945798562073790010097108820522876335350057042701) }

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
  base := (59269057685808708561146290895118713824573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-170835373863252131523317553955753216000000000000)
      constant := (4956302197848449001290011217273669834389987487437) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel109
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
  base := (61254491292073070840787483296284651139041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1550058890572399900717401001272367104000000000000)
      constant := (45356888400684199172830809798462885918264362415161) }

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
  base := (15313622821101287937552484346522758185347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-172416364064552619644080758582867056000000000000)
      constant := (5050353263973805724645152868861769681657651892172) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel110
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
  base := (31634592923980863231347955501948214010969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-12927870352100901838546219353393984000000000000)
      constant := (381897374708043700586570631364746355237520551538) }

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
  base := (31634592920719339628567558320925107446247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1437994663354157915411933580247776000000000000)
      constant := (42523092533312082649088424132263848451233326366) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel111
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
  base := (3265657068053955983040946872955724613967/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-175387303848446482690087120249886336000000000000)
      constant := (5230029875067137876920817773165217122725438676460) }

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
  base := (13062628271106080624322026186790675591549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-175578344467153595885607167837094736000000000000)
      constant := (5241124995516366499928926182544808213626040707905) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel112
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
  base := (13477271566052511342678774034448207534201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-32504064421792399305254604545658816000000000000)
      constant := (978345877723564514171035735862601698898564524645) }

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
  base := (33693178912771485294656378269853743115467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-3615496625886818040946334131922624000000000000)
      constant := (108935625733228262617049337812597970706053428054) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel113
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
  base := (34744417627277933550376140921467975678751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1606912578699636787704167163225586944000000000000)
      constant := (48815619738206129657604109962824281405439946784142) }

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
  base := (69488835250541796624480854624420525789141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-178740324869754572127133577091322416000000000000)
      constant := (5435456192764216748620764257485931804362777933029) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel114
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
  base := (8952571704147026897019450036368796145471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-498961526848706066312975901420096000000000000)
      constant := (15297101897458776936781800232738548738771980472) }

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
  base := (17905143407440607643325714010138041300063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-499505027897659446670074187585696000000000000)
      constant := (15329519642722509514137169756526177787472294108) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel115
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
  base := (73781572965486159521959198569752250044767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1635339422763255231197550244202196864000000000000)
      constant := (50592940988354691785733844524500977043084611091207) }

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
  base := (73781572962583088736993397696159468287239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-181902305272355548368659986345550096000000000000)
      constant := (5633346855702681579630094097861616884978489451191) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel116
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
  base := (75971833250970132626448635792532159503409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1649552844795064452944241784690501824000000000000)
      constant := (51493590508729574669518110132686443175337368161289) }

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
  base := (75971833248501537502238905424839962444691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-183483295473656036489423190972663936000000000000)
      constant := (5733626986802708718443797343327963221577780830979) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel117
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
  base := (78191354489214643987875019863027358997321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-184862918536319297187881480575422976000000000000)
      constant := (5822470291773361079854580645653252357349736951449) }

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
  base := (15638270897423128077768816302170589010691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-185064285674956524610186395599777776000000000000)
      constant := (5834796984322046630588648889328446979151118424895) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel118
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
  base := (80440136679891619621447903372235372998911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1677979688858682896437624865667111744000000000000)
      constant := (53318867340040397138772424052906228189632755243431) }

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
  base := (80440136678106990741398189982708499615067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-186645275876257012730949600226891616000000000000)
      constant := (5936856848260013808330013914322506256612601339723) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel119
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
  base := (10339772477843047934024162220325574058077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-34534553283479430983353396043988096000000000000)
      constant := (1107010094917654540745341372868017764831022023464) }

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
  base := (20679544955306785759024865729072105183773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-3841352368929744915341077650081744000000000000)
      constant := (123261358747266907889195068410207430506129553652) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel120
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
  base := (85025483917575864164251970291743452382067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-189600725880255704436778660738191296000000000000)
      constant := (6130679395414497726974005268069866561431552362723) }

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
  base := (21256370979071508151543836066325429844819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-189807256278857988972476009481119296000000000000)
      constant := (6143646175389833856789526893649176695806101592844) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel121
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
  base := (17472409792847735230619037091103048837727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-14219999627719921997336359397785344000000000000)
      constant := (463774603829204786301242707879782906390074880635) }

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
  base := (4368102448157111914501019973001883651727/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1581721045290565926390406728167216000000000000)
      constant := (51639468087446092772865084930454602398307978060) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel122
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
  base := (89727874962626779633302808670301710798909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1734833376985919783424391027620331584000000000000)
      constant := (57065332164772928616764102400660228509968550516789) }

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
  base := (44863937480847398496965405871589939469843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-192969236681458965214002418735346976000000000000)
      constant := (6353994968189292494476095756338614126306256784134) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel123
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
  base := (92122961912668470125467156870831001668617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-194338533224192111685675840900959616000000000000)
      constant := (6446881095894060744367031507277299328210456099673) }

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
  base := (736983695295010600405433467969430737437/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-194550226882759453334765623362460816000000000000)
      constant := (6460504164214635437755348495096581240257161781625) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel124
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
  base := (11818413726790060987156169197725431926979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1763260221049538226917774108596941504000000000000)
      constant := (58986520158153800063957493289637082056584360298072) }

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
  base := (94547309813647239904890670896880070430099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-196131217084059941455528827989574656000000000000)
      constant := (6567903226656921334079968393762127243466400566531) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel125
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
  base := (97000918667563070423789509396948937942159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1777473643081347448664465649085246464000000000000)
      constant := (59959103050094308018866585043426911812188888250039) }

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
  base := (97000918666990908209848279711745367670377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-197712207285360429576292032616688496000000000000)
      constant := (6676192155516114581950276146104608220855277149113) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel126
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
  base := (99483788472395798936616119081340822078229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-4062782460574051406828020838035264000000000000)
      constant := (138185212106276785707843690571817712449199120949) }

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
  base := (1554434194873587091259073364481445535337/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-4067208111972671789735821168240864000000000000)
      constant := (138476958179433060899731082131327601435459551808) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel127
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
  base := (10199591922883411356888861567304006270807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1805900487144965892157848730061856384000000000000)
      constant := (61928246624475360927076273688661353581805681700470) }

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
  base := (101995919228420942425208750141337192934627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-200874187687961405817818441870916176000000000000)
      constant := (6895439612485275437067164386675022478304294657363) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel128
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
  base := (104537310936906391369539734252680144679991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1820113909176775113904540270550161344000000000000)
      constant := (62924807306916749944820827466162342689297108910111) }

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
  base := (52268655468277659226379536083225525591509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-202455177889261893938581646498030016000000000000)
      constant := (7006398140595345803680173667594076077969545053642) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel129
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
  base := (107107963596651498111815078624228869804381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-203814147912064926183470201226496256000000000000)
      constant := (7103262287354775359362074683621025705834333156589) }

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
  base := (107107963596353207405386659842859692022937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-204036168090562382059344851125143856000000000000)
      constant := (7118246535122517780604185479049747880155441643753) }

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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565074048202458890251/100000000000000000000)
  centralHi := (141268512050614722563/25000000000000000000)
  directionLo := (567277074289133570669/100000000000000000000)
  directionHi := (56727707428913357067/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree130.table
  base := (109707877208116738853113334929293650186891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1848540753240393557397923351526771264000000000000)
      constant := (64941906462304957047895402064066054606811791325011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree130.table
  base := (109707877207863309169828472223040889247909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-205617158291862870180108055752257696000000000000)
      constant := (7230984796066895603567075119352230685078657738421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567277074289133570669/100000000000000000000)
  centralHi := (56727707428913357067/10000000000000000000)
  directionLo := (284735788967668895077/50000000000000000000)
  directionHi := (113894315587067558031/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree131.table
  base := (56168525885678072012920971891829856267693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1862754175272202779144614892015076224000000000000)
      constant := (65962444935253727191294250531963120941336864376906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree131.table
  base := (112337051771140840614204095059521403049187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-207198148493163358300871260379371536000000000000)
      constant := (7344612923428597457041642838139074441922985330003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284735788967668895077/50000000000000000000)
  centralHi := (113894315587067558031/20000000000000000000)
  directionLo := (71457207161249644361/12500000000000000000)
  directionHi := (571657657289997154889/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree132.table
  base := (57497743643214518900513922191511225924881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1723569878148771350680722160241856000000000000)
      constant := (61516047754858063769517693650738836150770440018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree132.table
  base := (114995487286246135014958428937233649573683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1725447427226973937368879876086656000000000000)
      constant := (61645710059568202285144295296118598027308878587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71457207161249644361/12500000000000000000)
  centralHi := (571657657289997154889/100000000000000000000)
  directionLo := (143458852158121496469/25000000000000000000)
  directionHi := (573835408632485985877/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree133.table
  base := (117683183753398843860635568098741503334043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (158994)
      previous := (79497)
      next := (79497)
      square := (768665769234066505039004719920000000000000)
      linear := (-106912828273832394292384983492096000000000000)
      constant := (3845751578476244646942825501925577497130772827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree133.table
  base := (58841591876621737136824575606517582607517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85407307692674056115444968880000000000000)
      linear := (-11892143642702489374322893868144000000000000)
      constant := (428206160744219472493576850118869254991019114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143458852158121496469/25000000000000000000)
  centralHi := (573835408632485985877/100000000000000000000)
  directionLo := (576004926422106659533/100000000000000000000)
  directionHi := (288002463211053329767/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree134.table
  base := (60200070586166045393872626337607420123547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1905394441367630444384689513479991104000000000000)
      constant := (69072015935132589097046414147778518387643491039174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree134.table
  base := (120400141172200116817691349542056194864449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-211941119097064822663160874260713056000000000000)
      constant := (7690836504018978732203934354655381579745825841681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576004926422106659533/100000000000000000000)
  centralHi := (288002463211053329767/50000000000000000000)
  directionLo := (289083151672948955169/50000000000000000000)
  directionHi := (578166303345897910339/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree135.table
  base := (61573179771648792621922357021383828530939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-213289762599937740681264561552032896000000000000)
      constant := (7791613866160072166848474228240032727377874752982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree135.table
  base := (61573179771592744968992836625148648704913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-213522109298365310783924078887826896000000000000)
      constant := (7808024097051342526318817821435702836159771865794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289083151672948955169/50000000000000000000)
  centralHi := (578166303345897910339/100000000000000000000)
  directionLo := (290159815182420279189/50000000000000000000)
  directionHi := (580319630364840558379/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree136.table
  base := (125921838866365726124655788556719478405967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1933821285431248887878072594456601024000000000000)
      constant := (71185026252591828890067537283128858883486710636407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree136.table
  base := (7870114929141907515760448608827127020829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-215103099499665798904687283514940736000000000000)
      constant := (7926101556501741440417192227992523600551115934416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290159815182420279189/50000000000000000000)
  centralHi := (580319630364840558379/100000000000000000000)
  directionLo := (145616249189631458533/25000000000000000000)
  directionHi := (582464996758525834133/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree137.table
  base := (128726579141607937117724222367280438776693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1948034707463058109624764134944905984000000000000)
      constant := (72253520306587503119760419244960223437176284577453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree137.table
  base := (128726579141527080140403856721208799429831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-216684089700966287025450488142054576000000000000)
      constant := (8045068882370329307913525362847094248826827947639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145616249189631458533/25000000000000000000)
  centralHi := (582464996758525834133/100000000000000000000)
  directionLo := (292301245084174181789/50000000000000000000)
  directionHi := (584602490168348363579/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree138.table
  base := (131560580369096198650797531689341213285409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-218027569943874147930161741714801216000000000000)
      constant := (8147778550825450974755592405717170251338477575921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree138.table
  base := (65780290184513765751858395465735656788527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-218265079902266775146213692769168416000000000000)
      constant := (8164926074657261009977543815564482691969605492926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292301245084174181789/50000000000000000000)
  centralHi := (584602490168348363579/100000000000000000000)
  directionLo := (146683049159820734323/25000000000000000000)
  directionHi := (586732196639282937293/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree139.table
  base := (134423842548902663224566686602296836366237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-1976461551526676553118147215921515904000000000000)
      constant := (74414486205117885745969037381052567392207296893077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree139.table
  base := (134423842548844351145859600805700378219981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-219846070103567263266976897396282256000000000000)
      constant := (8285673133362691673713220918958701596830322512989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146683049159820734323/25000000000000000000)
  centralHi := (586732196639282937293/100000000000000000000)
  directionLo := (588854200660301407321/100000000000000000000)
  directionHi := (294427100330150703661/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree140.table
  base := (68658182840549670327468306397084102671503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-40626019868540526017649770538975936000000000000)
      constant := (1540958327543987167091131916791098392398290605774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree140.table
  base := (137316365681049824565800811974108066520967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-4518919598058525538525308204559104000000000000)
      constant := (171577756295648490137993845658456374453702359527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588854200660301407321/100000000000000000000)
  centralHi := (294427100330150703661/50000000000000000000)
  directionLo := (147742146300870856351/25000000000000000000)
  directionHi := (118193717040696685081/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree141.table
  base := (140238149765757841883007601658162739387399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-222765377287810555179058921877569536000000000000)
      constant := (8511935832338099395759459809209909500339867810231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree141.table
  base := (1752976872071447463025313956121499203353/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-223008050506168239508503306650509936000000000000)
      constant := (8529836850029667814529841372326307206270516580560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147742146300870856351/25000000000000000000)
  centralHi := (118193717040696685081/20000000000000000000)
  directionLo := (593075431761872246619/100000000000000000000)
  directionHi := (29653771588093612331/5000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree142.table
  base := (14318919480294917180808146021395953770223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2019101817622104218358221837386430784000000000000)
      constant := (77715879529281823659245883845928792023769658905830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree142.table
  base := (143189194802913472653901955025007560300933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-224589040707468727629266511277623776000000000000)
      constant := (8653253507991519470021805614507233478833747664277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593075431761872246619/100000000000000000000)
  centralHi := (29653771588093612331/5000000000000000000)
  directionLo := (119034964077224893037/20000000000000000000)
  directionHi := (297587410193062232593/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree143.table
  base := (146169500792743563113078567253430816688617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (23243346)
      previous := (11621673)
      next := (11621673)
      square := (112371312330424813286239293311280000000000000)
      linear := (-16804258178957962314916639486568064000000000000)
      constant := (651506852598128193342260223851174111447644515017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree143.table
  base := (2923390015854265067424822123912399473089/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-1869173809163381948347353024006096000000000000)
      constant := (72541818449359352639928189668206109713973566050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119034964077224893037/20000000000000000000)
  centralHi := (297587410193062232593/50000000000000000000)
  directionLo := (119453365944000063227/20000000000000000000)
  directionHi := (74658353715000039517/12500000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree144.table
  base := (149179067735210344327282298675587311681351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-227503184631746962427956102040337856000000000000)
      constant := (8884085710702143696116887952553924362716101558519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree144.table
  base := (1864738346689807644933246731365747571019/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-227751021110069703870792920531851456000000000000)
      constant := (8902756423172703109330993946705087565026749280880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119453365944000063227/20000000000000000000)
  centralHi := (74658353715000039517/12500000000000000000)
  directionLo := (18729735532335595639/3125000000000000000)
  directionHi := (599351537034739060449/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree145.table
  base := (152217895630417836445832010417005320362601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2061742083717531883598296458851345664000000000000)
      constant := (81089206225120485360421806160048072224852619457921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree145.table
  base := (38054473907598997645855932094607508859851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-229332011311370191991556125158965296000000000000)
      constant := (9028842680392330283551246249694830936523401700076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18729735532335595639/3125000000000000000)
  centralHi := (599351537034739060449/100000000000000000000)
  directionLo := (120285803652472393029/20000000000000000000)
  directionHi := (300714509131180982573/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree146.table
  base := (155285984478433273330482030139163982823131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2075955505749341105344987999339650624000000000000)
      constant := (82229633650778382827983974084062578376760458678051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree146.table
  base := (4852687014950460252971543401880813025313/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-230913001512670680112319329786079136000000000000)
      constant := (9155818804031507319740870907043785900613637135904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120285803652472393029/20000000000000000000)
  centralHi := (300714509131180982573/50000000000000000000)
  directionLo := (150874837006985871843/25000000000000000000)
  directionHi := (603499348027943487373/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree147.table
  base := (989895839245767136740486266360060518949/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-4739612081136395299527618004145024000000000000)
      constant := (189065881345338455149328862502330976564513803040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree147.table
  base := (31676666855861399861751537860409080029971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-4744775341101452412920051722718224000000000000)
      constant := (189462954981436241983709899620680193123945816255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150874837006985871843/25000000000000000000)
  centralHi := (603499348027943487373/100000000000000000000)
  directionLo := (12111251993617789331/2000000000000000000)
  directionHi := (605562599680889466551/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree148.table
  base := (8075497251657556929421403065789354507791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2104382349812959548838371080316260544000000000000)
      constant := (84534466292669363161116445084553995517327500678220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree148.table
  base := (80754972516568887866567964371614059246471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-234074981915271656353845739040306816000000000000)
      constant := (9412440650569074958937109105740737752750619775598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12111251993617789331/2000000000000000000)
  centralHi := (605562599680889466551/100000000000000000000)
  directionLo := (6076188453252594157/1000000000000000000)
  directionHi := (607618845325259415701/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree149.table
  base := (16466581673998213969269983027075644190673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2118595771844768770585062620804565504000000000000)
      constant := (85698871508904922764475380820981290189267192050330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree149.table
  base := (82332908369985398665240960915196301031443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-235655972116572144474608943667420656000000000000)
      constant := (9542086373467741051986120776503464427284737244934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6076188453252594157/1000000000000000000)
  centralHi := (607618845325259415701/100000000000000000000)
  directionLo := (609668155849168376693/100000000000000000000)
  directionHi := (304834077924584188347/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree150.table
  base := (167850949399878182481082114823978846243597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-236978799319619776925750462365874496000000000000)
      constant := (9652363258000237808942934578330347179155561467293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree150.table
  base := (4196273734996713888338903670770525786761/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-237236962317872632595372148294534496000000000000)
      constant := (9672621962786507891074266205809973980307354192360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609668155849168376693/100000000000000000000)
  centralHi := (304834077924584188347/50000000000000000000)
  directionLo := (305855300476651129821/50000000000000000000)
  directionHi := (611710600953302259643/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree151.table
  base := (171065343012900455823697742341758046749637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2147022615908387214078445701781175424000000000000)
      constant := (88051659731962194409996339569514192382871264164477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree151.table
  base := (171065343012892285208134580547589706852661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-238817952519173120716135352921648336000000000000)
      constant := (9804047418525506541409971455354290029266523171909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305855300476651129821/50000000000000000000)
  centralHi := (611710600953302259643/100000000000000000000)
  directionLo := (613746249178579119077/100000000000000000000)
  directionHi := (306873124589289559539/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree152.table
  base := (174308997579108898223721161370337400233227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (7790706)
      previous := (3895353)
      next := (3895353)
      square := (37664622692469258746911231276080000000000000)
      linear := (-5986803429197220043836945269444544000000000000)
      constant := (247202334456471578303689957994317902013845225947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree152.table
  base := (17430899757910196392956743506600618183797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4184958076941028749656803475120000000000000)
      linear := (-665925049087184512013569411492416000000000000)
      constant := (27524550528212923482371776407831662652117324130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613746249178579119077/100000000000000000000)
  centralHi := (306873124589289559539/50000000000000000000)
  directionLo := (615775167932987424909/100000000000000000000)
  directionHi := (61577516793298742491/10000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree153.table
  base := (88790956549281101000966081678627352341347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-241716606663556184174647642528642816000000000000)
      constant := (10048490926941711884712114788582645623006993074086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree153.table
  base := (177581913098556317207683737051417183976963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-241979932921774096957661762175876016000000000000)
      constant := (10069567929264710092513732933403476054651588319347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615775167932987424909/100000000000000000000)
  centralHi := (61577516793298742491/10000000000000000000)
  directionLo := (617797423517631060111/100000000000000000000)
  directionHi := (38612338969851941257/6250000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree154.table
  base := (36176817914263564488709897620285501631681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (474354)
      previous := (237177)
      next := (237177)
      square := (2293292088376016597678352924720000000000000)
      linear := (-369314029685244540279730194509376000000000000)
      constant := (15456364739927610520143283773547201974006657845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree154.table
  base := (4522102239282820712948501821671444515233/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (254810232041779621964261436080000000000000)
      linear := (-41079595736730407333180125957664000000000000)
      constant := (1720975372620199649753991557459991658799964520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617797423517631060111/100000000000000000000)
  centralHi := (38612338969851941257/6250000000000000000)
  directionLo := (619813081152009515981/100000000000000000000)
  directionHi := (309906540576004757991/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree155.table
  base := (184215526997431990929926853925554628017493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2203876304035624101065211863734395264000000000000)
      constant := (92853147340453510405342854114895141222536561274253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree155.table
  base := (92107763498713876592375837690846011852249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-245141913324375073199188171430103696000000000000)
      constant := (10338647905686346676921723623119041555084372679762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619813081152009515981/100000000000000000000)
  centralHi := (309906540576004757991/50000000000000000000)
  directionLo := (621822204998560556021/100000000000000000000)
  directionHi := (310911102499280278011/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree156.table
  base := (23447028172119966404909199481228780388973/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-246454414007492591423544822691411136000000000000)
      constant := (10452611192749398866372365131948410523618926008296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree156.table
  base := (11723514086059758457564711823824331514259/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-246722903525675561319951376057217536000000000000)
      constant := (10474522693528376767817575683947857545901488345136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621822204998560556021/100000000000000000000)
  centralHi := (310911102499280278011/50000000000000000000)
  directionLo := (623824858186491477663/100000000000000000000)
  directionHi := (19494526818327858677/3125000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree157.table
  base := (190966184709954878336400427703140793992351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2232303148099242544558594944711005184000000000000)
      constant := (95301846725905077990162998196007999550869528857671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree157.table
  base := (190966184709951827160863865874998869758497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-248303893726976049440714580684331376000000000000)
      constant := (10611287347791369259731361973919831867866124465393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623824858186491477663/100000000000000000000)
  centralHi := (19494526818327858677/3125000000000000000)
  directionLo := (19556909463591375439/3125000000000000000)
  directionHi := (625821102834924014049/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree158.table
  base := (38877080999294019817129602259473911308331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2246516570131051766305286485199310144000000000000)
      constant := (96538185313935989522491847762146804895289550136255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree158.table
  base := (194385404996467510233761505750876772773703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-249884883928276537561477785311445216000000000000)
      constant := (10748941868475436910575749104154468655264877916407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19556909463591375439/3125000000000000000)
  centralHi := (625821102834924014049/100000000000000000000)
  directionLo := (313905500037688441443/50000000000000000000)
  directionHi := (627811000075376882887/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree159.table
  base := (197833886236556914417053622074888783518721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-251192221351428998672442002854179456000000000000)
      constant := (10864724055426479650950151273862660494691181348049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree159.table
  base := (49458471559138679480730245308094008133027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-251465874129577025682240989938559056000000000000)
      constant := (10887486255580690020806587791734295660374715467852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313905500037688441443/50000000000000000000)
  centralHi := (627811000075376882887/100000000000000000000)
  directionLo := (314897305036804501661/50000000000000000000)
  directionHi := (629794610073609003323/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree160.table
  base := (201311628430265722556332701784301363480843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2274943414194670209798669566175920064000000000000)
      constant := (99034840280613030835541326312919556965469156059603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree160.table
  base := (201311628430263859028312065175852076228849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-253046864330877513803004194565672896000000000000)
      constant := (11026920509107236483856660539418097492545865305281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314897305036804501661/50000000000000000000)
  centralHi := (629794610073609003323/100000000000000000000)
  directionLo := (315885996025422731037/50000000000000000000)
  directionHi := (25270879682033818483/4000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree161.table
  base := (51204657894411455749206833611282822918859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (57396834)
      previous := (28698417)
      next := (28698417)
      square := (277488342693498008319080703891120000000000000)
      linear := (-46717486453601621051946145033963776000000000000)
      constant := (2046839931821654716845451596610014355565072479244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree161.table
  base := (102409315788822121010837032667420068468327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-5196486827187306161709538759036464000000000000)
      constant := (227902951613371057919394194644959196021529983374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315885996025422731037/50000000000000000000)
  centralHi := (25270879682033818483/4000000000000000000)
  directionLo := (316871602152203707207/50000000000000000000)
  directionHi := (126748640860881482883/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree162.table
  base := (208354895678745440948250193426107447376739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-255930028695365405921339183016947776000000000000)
      constant := (11284829514975932967322639419171928843034303476691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree162.table
  base := (208354895678744099735736313951462661482083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-256208844733478490044530603819900576000000000000)
      constant := (11308458615424629319447508834410744377293744508627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316871602152203707207/50000000000000000000)
  centralHi := (126748640860881482883/20000000000000000000)
  directionLo := (158927076056941562883/25000000000000000000)
  directionHi := (635708304227766251533/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree163.table
  base := (105960210366805876022277780229852734205967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2317583680290097875038744187640834944000000000000)
      constant := (102839767207180886336351445757226639795474444872814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree163.table
  base := (211920420733610614276388547335869967332113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-257789834934778978165293808447014416000000000000)
      constant := (11450562468215679915165041538857748934108667369697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158927076056941562883/25000000000000000000)
  centralHi := (635708304227766251533/100000000000000000000)
  directionLo := (637667348330041551319/100000000000000000000)
  directionHi := (15941683708251038783/2500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree164.table
  base := (215515206742290907133052287835362542703207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2331797102321907096785435728129139904000000000000)
      constant := (104124061376454439035356333595721557507468084170447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree164.table
  base := (43103041348457988397069769186415747059789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-259370825136079466286057013074128256000000000000)
      constant := (11593556187428432416805880437065893814593067610705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637667348330041551319/100000000000000000000)
  centralHi := (15941683708251038783/2500000000000000000)
  directionLo := (639620392254961552413/100000000000000000000)
  directionHi := (319810196127480776207/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree165.table
  base := (43827850740965611400032364527382554762001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-2154279636688444736944102175038976000000000000)
      constant := (96801054309095431181827967919644190055925178445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree165.table
  base := (219139253704827238313350766199228897158727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12485701370047201476248810367920000000000000)
      linear := (-2156626573036197970304299319844976000000000000)
      constant := (97003634488123830361131873227603899961840721903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639620392254961552413/100000000000000000000)
  centralHi := (319810196127480776207/50000000000000000000)
  directionLo := (320783745399652074897/50000000000000000000)
  directionHi := (128313498159860829959/20000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree166.table
  base := (111396280810633688458524713161061281376549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2360223946385525540278818809105749824000000000000)
      constant := (106716627505633193863743134639049418311655570518458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree166.table
  base := (55698140405316670622750954442681734754357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-262532805538680442527583422328355936000000000000)
      constant := (11882213225119427645693910654804827783737793350932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320783745399652074897/50000000000000000000)
  centralHi := (128313498159860829959/20000000000000000000)
  directionLo := (128701739586167140437/20000000000000000000)
  directionHi := (321754348965417851093/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree167.table
  base := (226475130491652090911587741123193636177593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2374437368417334762025510349594054784000000000000)
      constant := (108024899465540079593877589973829301926846186966353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree167.table
  base := (226475130491651501907123583675762752661863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-264113795739980930648346626955469776000000000000)
      constant := (12027876543597857455359714240492765619152119047447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128701739586167140437/20000000000000000000)
  centralHi := (321754348965417851093/50000000000000000000)
  directionLo := (322722033402882132749/50000000000000000000)
  directionHi := (645444066805764265499/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree168.table
  base := (46037392063204899138496197099440320087839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-5416441701698739192227215170254784000000000000)
      constant := (247939147442916998917213233385544095108784476795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree168.table
  base := (230186960316023996123196186583856927584879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30832038077055334257675633765680000000000000)
      linear := (-5422342570230233036104282277195584000000000000)
      constant := (248457749561191090599275222622365806453835099599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell117.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322722033402882132749/50000000000000000000)
  centralHi := (645444066805764265499/100000000000000000000)
  directionLo := (5057606638950962663/781250000000000000)
  directionHi := (129474729957144644173/20000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree169.table
  base := (233928051094425984167501980627261434885557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (2812444866)
      previous := (1406222433)
      next := (1406222433)
      square := (13596928791981402407634954490664880000000000000)
      linear := (-2402864212480953205518893430570664704000000000000)
      constant := (110665421175992942014453023736162293987121082754797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree169.table
  base := (233928051094425560468339980492212751385307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1510769865775711378626106054518320000000000000)
      linear := (-267275776142581906889873036209697456000000000000)
      constant := (12321872779821034198987415381040944478469818158283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell117.Kernel169
