import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell044.Parameters
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch000_049
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch050_099
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch100_149
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch000_049
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch050_099
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree000.table
  base := (2695714724960978339096229203/50000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (445205157323319902773484100000000000000)
      linear := (16627653420868695414297500000000000000)
      constant := (269571472496097833909622920300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree000.table
  base := (2695714724960978339096229203/50000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (445205157323319902773484100000000000000)
      linear := (16627653420868695414297500000000000000)
      constant := (269571472496097833909622920300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree001.table
  base := (327824719219487441234610199738312057303429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-7738385660217338963906899508693750000000000)
      constant := (3086286789753771852715887667052458274121088461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree001.table
  base := (163617668503967751209177426323059593943811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-11641316693654416282242402354993750000000000)
      constant := (4621127542911083137245954297086065951220703097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49961995729029094919/100000000000000000000)
  directionHi := (1249049893225727373/2500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree002.table
  base := (204267476131213186057804269242355249531433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-15789670502508585038120049372387500000000000)
      constant := (1929389411148104301293567959905197300653753097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree002.table
  base := (203579653353072214378330235693319538978049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-47503964320839386459888360484975000000000000)
      constant := (5768880412999758469938580165736145470483389123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49961995729029094919/100000000000000000000)
  centralHi := (1249049893225727373/2500000000000000000)
  directionLo := (35328465981609798181/50000000000000000000)
  directionHi := (70656931963219596363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree003.table
  base := (13114848434209213508153172267385458102803/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-11920477672399915556166599618040625000000000)
      constant := (625467127005229822795436928652943822735429635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree003.table
  base := (130539490897139284456290582360853731765539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-23908431751456646785097305419987500000000000)
      constant := (1245300379554601754401684523723962019994456451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35328465981609798181/50000000000000000000)
  centralHi := (70656931963219596363/100000000000000000000)
  directionLo := (86536715050217642091/100000000000000000000)
  directionHi := (21634178762554410523/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree004.table
  base := (87149389491294940197728635017210548665691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-31892240187091077186546349099775000000000000)
      constant := (850336922159794549259031888782753583645486619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree004.table
  base := (4333120814148606772205929486735147123343/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-47973313093950247125347736017475000000000000)
      constant := (1268889713220811066718900850562672166006028610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86536715050217642091/100000000000000000000)
  centralHi := (21634178762554410523/25000000000000000000)
  directionLo := (99923991458058189839/100000000000000000000)
  directionHi := (1249049893225727373/1250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree005.table
  base := (75096020736531502088384240423987754321/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-19971762514691161630379749481734375000000000)
      constant := (306434975159498243592478647419003149076578100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree005.table
  base := (59703815767223251549515169668008956713947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-120167957121431048146099027809937500000000000)
      constant := (1828886564199738752367598194475153469602081969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/100000000000000000000)
  centralHi := (1249049893225727373/1250000000000000000)
  directionLo := (13964802342707902391/12500000000000000000)
  directionHi := (111718418741663219129/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree006.table
  base := (4291921515709227662546552391019532669359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-23997404935836784667486324413581250000000000)
      constant := (236280830016562150278875914188428074586244155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree006.table
  base := (10659281056763146863475355091358657468577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-24064881342493600340250430597487500000000000)
      constant := (235147283035958193464486065040721981868681986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13964802342707902391/12500000000000000000)
  centralHi := (111718418741663219129/100000000000000000000)
  directionLo := (61190698033616860211/50000000000000000000)
  directionHi := (122381396067233720423/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree007.table
  base := (3955314468924363131144896564088393210527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-28023047356982407704592899345428125000000000)
      constant := (195727745954137316958283818419834502222956672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree007.table
  base := (6285542961826867175341264675337185662917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-168610618988492155936906139359912500000000000)
      constant := (1169885416300825796587078150636429909473290795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61190698033616860211/50000000000000000000)
  centralHi := (122381396067233720423/100000000000000000000)
  directionLo := (132187015703482203447/100000000000000000000)
  directionHi := (16523376962935275431/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree008.table
  base := (239114060575005860848077926185024802661/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-32048689778128030741699474277275000000000000)
      constant := (173789246188035143349037383675696480911867450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree008.table
  base := (23744472444103851823186230380409037487207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-192831949922022709832309695134900000000000000)
      constant := (1040091333392012825501454514484593401151391989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132187015703482203447/100000000000000000000)
  centralHi := (16523376962935275431/12500000000000000000)
  directionLo := (5652554557057567709/4000000000000000000)
  directionHi := (70656931963219596363/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree009.table
  base := (9182359664343184096353385663854158280593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-36074332199273653778806049209121875000000000)
      constant := (164061721758297503932596258568561416863662037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree009.table
  base := (284862095414604972207661052362646621307/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-36175546809258877287952208484981250000000000)
      constant := (163869890358433128806211098292334956072332016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5652554557057567709/4000000000000000000)
  centralHi := (70656931963219596363/50000000000000000000)
  directionLo := (149885987187087284759/100000000000000000000)
  directionHi := (3747149679677182119/2500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree010.table
  base := (14201988283589380077557838248416694889783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-80199949240838553631825248281937500000000000)
      constant := (325558748679505541400459460079396627530468247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree010.table
  base := (14091614860889171562565374242626235565241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-241274611789083817623116806684875000000000000)
      constant := (976794965861159188041406463273231845050057707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/100000000000000000000)
  centralHi := (3747149679677182119/2500000000000000000)
  directionLo := (7899685147566834391/5000000000000000000)
  directionHi := (157993702951336687821/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree011.table
  base := (2736713682619361745177144085041016767203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-44125617041564899853019199072815625000000000)
      constant := (167701176819396927499857502122246409189288554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree011.table
  base := (5426342956985955692245283708254820626877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-132747971361307185759260181229931250000000000)
      constant := (503731881309085162479148858564100521053607079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7899685147566834391/5000000000000000000)
  centralHi := (157993702951336687821/100000000000000000000)
  directionLo := (33141038722105700917/20000000000000000000)
  directionHi := (82852596805264252293/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree012.table
  base := (8311376184072617377820111649203704925217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-96302518925421045780251548009325000000000000)
      constant := (354945007550479702770454684601608440891366753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree012.table
  base := (8228763821066762455894541307984253814521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-96572424552048308471307972744950000000000000)
      constant := (355721146482542901779222260019726969140828089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/20000000000000000000)
  centralHi := (82852596805264252293/50000000000000000000)
  directionLo := (173073430100435284183/100000000000000000000)
  directionHi := (21634178762554410523/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree013.table
  base := (1223592376067399110028378587148808118591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-104353803767712291854464697873018750000000000)
      constant := (382515758915730523894954564535544633017238595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree013.table
  base := (6043846612149484344669072453827945743577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-313938604589675479309327474009837500000000000)
      constant := (1150925988741660094502394828369800447941447979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/100000000000000000000)
  centralHi := (21634178762554410523/12500000000000000000)
  directionLo := (9007026871276361939/5000000000000000000)
  directionHi := (180140537425527238781/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree014.table
  base := (170171308050085505381753164967478670273/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-112405088610003537928677847736712500000000000)
      constant := (417057703063110780065023617115998803027466425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree014.table
  base := (837332823267750552620647085124766899657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-338159935523206033204731029784825000000000000)
      constant := (1255610587386797351783265569992136320133090695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9007026871276361939/5000000000000000000)
  centralHi := (180140537425527238781/100000000000000000000)
  directionLo := (23367583797186227977/12500000000000000000)
  directionHi := (186940670377489823817/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree015.table
  base := (264709176398691619083946505211570079403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-60228186726147392001445498800203125000000000)
      constant := (228940830036031196597973742859895721612076635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree015.table
  base := (258466157689245293415705093568266772319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-60396877742789431183355764259968750000000000)
      constant := (229861538710746800561461918262097332959997355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/12500000000000000000)
  centralHi := (186940670377489823817/100000000000000000000)
  directionLo := (24187747175226971863/12500000000000000000)
  directionHi := (38700395480363154981/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree016.table
  base := (1246923077333603929631789187520736995967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-128507658294586030077104147464100000000000000)
      constant := (504522204431311857221789688842245114395053503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree016.table
  base := (1188818889747676091831887273287520460987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-386602597390267140995538141334800000000000000)
      constant := (1520218232897326723521069269812736840052280049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24187747175226971863/12500000000000000000)
  centralHi := (38700395480363154981/20000000000000000000)
  directionLo := (99923991458058189839/50000000000000000000)
  directionHi := (199847982916116379679/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree017.table
  base := (9535946922131166636307849382036439459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-68279471568438638075658648663896875000000000)
      constant := (278326399586060759314999222996738925585432231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree017.table
  base := (-35284575785081342533755491137007209333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-410823928323797694890941697109787500000000000)
      constant := (1677785998142862494725280692200470033439657409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/50000000000000000000)
  centralHi := (199847982916116379679/100000000000000000000)
  directionLo := (51499646414361347701/25000000000000000000)
  directionHi := (41199717131489078161/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree018.table
  base := (-212355906845913054738387049250087042827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-144610227979168522225530447191487500000000000)
      constant := (614035229605926148561228201833297037882703785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree018.table
  base := (-55639353629296525244385960876609157257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-72507543209554708131057542147462500000000000)
      constant := (308527158422840203324501007425870235018688870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/25000000000000000000)
  centralHi := (41199717131489078161/20000000000000000000)
  directionLo := (6624087371551837159/3125000000000000000)
  directionHi := (211970795889658789089/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree019.table
  base := (-402961483777873401874806413479313075869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-152661512821459768299743597055181250000000000)
      constant := (676489066754003745312161563699110296423867895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree019.table
  base := (-82510087242592476425894912819256100457/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-459266590190858802681748808659762500000000000)
      constant := (2039810982395631508257559254525045474747506525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/3125000000000000000)
  centralHi := (211970795889658789089/100000000000000000000)
  directionLo := (217779290400448565969/100000000000000000000)
  directionHi := (21777929040044856597/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree020.table
  base := (-2855038961062064944420790526654584695577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-160712797663751014373956746918875000000000000)
      constant := (743872919682832899120079819386445293849316007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree020.table
  base := (-181258550062131443835259012905000849119/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-241743960562194678288576182217375000000000000)
      constant := (1121653952654379229395784083296649015755343896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/100000000000000000000)
  centralHi := (21777929040044856597/10000000000000000000)
  directionLo := (223436837483326438257/100000000000000000000)
  directionHi := (111718418741663219129/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree021.table
  base := (-3594600184899413787451428222434743959653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-168764082506042260448169896782568750000000000)
      constant := (816072694631169749931584750511859980411749923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree021.table
  base := (-909255809287175155999228380319285221921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-84618208676319985078759320034956250000000000)
      constant := (410218778676590177786337411814319757100140622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/100000000000000000000)
  centralHi := (111718418741663219129/50000000000000000000)
  directionLo := (57238656824834053731/25000000000000000000)
  directionHi := (9158185091973448597/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree022.table
  base := (-2121757908399928171223157478622239132573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-88407683674166753261191523323131250000000000)
      constant := (446497034474165674702012528801780949657870643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree022.table
  base := (-214170452825371111508193145296093492097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-265965291495725232183979737992362500000000000)
      constant := (1346771540662434121681000870053757236860779810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57238656824834053731/25000000000000000000)
  centralHi := (9158185091973448597/4000000000000000000)
  directionLo := (234342532159668944469/100000000000000000000)
  directionHi := (23434253215966894447/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree023.table
  base := (-962047153892596485825635270715394452807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-184866652190624752596596196509956250000000000)
      constant := (974557537405727256923629615279512676170819685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree023.table
  base := (-4847727235456601471296095630930074682363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-556151913924981018263363031759712500000000000)
      constant := (2939761095480282951567254222241234242878439599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/100000000000000000000)
  centralHi := (23434253215966894447/10000000000000000000)
  directionLo := (239609314084893192001/100000000000000000000)
  directionHi := (119804657042446596001/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree024.table
  base := (-42415935025641748220129090958256006419/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-192917937032915998670809346373650000000000000)
      constant := (1060695055664865215739898486215599279450453625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree024.table
  base := (-1334299727211613830680450527168715504649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-96728874143085262026461097922450000000000000)
      constant := (533293813925394686128532181086170361633515118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239609314084893192001/100000000000000000000)
  centralHi := (119804657042446596001/50000000000000000000)
  directionLo := (48952558426893488169/20000000000000000000)
  directionHi := (122381396067233720423/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree025.table
  base := (-572504712784031082759357997993959056197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-100484610937603622372511248118671875000000000)
      constant := (575673847650816343975639000595351369052774635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree025.table
  base := (-5758080098738695533005188298220532420117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-604594575792042126054170143309687500000000000)
      constant := (3473371856806387801447096491328370242314857441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/20000000000000000000)
  centralHi := (122381396067233720423/50000000000000000000)
  directionLo := (124904989322572737299/50000000000000000000)
  directionHi := (249809978645145474599/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree026.table
  base := (-608487524716023104380470552727807980039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-104510253358749245409617823050518750000000000)
      constant := (623231977000913005848281348996693808735315245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree026.table
  base := (-6115839751167041056627553296360562446743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-628815906725572679949573699084675000000000000)
      constant := (3760433643302648220666820807070088997565785339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124904989322572737299/50000000000000000000)
  centralHi := (249809978645145474599/100000000000000000000)
  directionLo := (127378595580179364343/50000000000000000000)
  directionHi := (254757191160358728687/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree027.table
  base := (-6386294085248133365231284632566574376589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-217071791559789736893448795964731250000000000)
      constant := (1345998500623421789210682187443837400518799099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree027.table
  base := (-1283058429527616791479518553064585873913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-217679079219701077948325751619887500000000000)
      constant := (1353604116772354266748412660428156440374262915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127378595580179364343/50000000000000000000)
  centralHi := (254757191160358728687/100000000000000000000)
  directionLo := (10384405806026117051/4000000000000000000)
  directionHi := (64902536287663231569/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree028.table
  base := (-265342700137907340646979863656189383913/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-225123076402080982967661945828425000000000000)
      constant := (1449911216495037469693686673549754883419064575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree028.table
  base := (-166517455149821723741317846094586814541/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-338629284296316893870190405317325000000000000)
      constant := (2187193852460866185515373011334054147219023860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10384405806026117051/4000000000000000000)
  centralHi := (64902536287663231569/25000000000000000000)
  directionLo := (52874806281392881379/20000000000000000000)
  directionHi := (16523376962935275431/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree029.table
  base := (-3415242619807011890774867103102647404183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-116587180622186114520937547846059375000000000)
      constant := (779083221986597009693403612716619324363104653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree029.table
  base := (-6855844989175626984186062404416402372473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-701479899526164341635784366409637500000000000)
      constant := (4701052809690930125975306802673030983669704629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52874806281392881379/20000000000000000000)
  centralHi := (16523376962935275431/6250000000000000000)
  directionLo := (10762143243766875203/4000000000000000000)
  directionHi := (67263395273542970019/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree030.table
  base := (-6980426945213844077267186385955263283207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-241225646086663475116088245555812500000000000)
      constant := (1670732383917241352871244875649629935580805337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree030.table
  base := (-1751027383855857571386062568816820558469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-120950205076615815921864653697437500000000000)
      constant := (840118723494389704566107184871499211355730358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10762143243766875203/4000000000000000000)
  centralHi := (67263395273542970019/25000000000000000000)
  directionLo := (273653120787660021997/100000000000000000000)
  directionHi := (136826560393830010999/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree031.table
  base := (-7086414553134233406608719297065626091329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-249276930928954721190301395419506250000000000)
      constant := (1787580602960644849715120545439167776059810439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree031.table
  base := (-3554255556347867154982617323687983684101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-374961280696612724713295738979806250000000000)
      constant := (2696640536935632563065763062352259577517631073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273653120787660021997/100000000000000000000)
  centralHi := (136826560393830010999/50000000000000000000)
  directionLo := (139088309657976977641/50000000000000000000)
  directionHi := (278176619315953955283/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree032.table
  base := (-3575577914497664709894300715570313844369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-128664107885622983632257272641600000000000000)
      constant := (954342811868342317383784091282173917038332079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree032.table
  base := (-1792938678796408519015940455481504662951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-387071946163378001660997516867300000000000000)
      constant := (2879341327267311164544758702628047135757764246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139088309657976977641/50000000000000000000)
  centralHi := (278176619315953955283/100000000000000000000)
  directionLo := (282627727852878385451/100000000000000000000)
  directionHi := (70656931963219596363/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree033.table
  base := (-897135138579886209680122022353357130309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-132689750306768606669363847573446875000000000)
      constant := (1017012289607711864670290565931288177020252976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree033.table
  base := (-3598133891135092064423102051843057262453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-133060870543381092869566431584931250000000000)
      constant := (1022808093937518952938120346639502521873829723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282627727852878385451/100000000000000000000)
  centralHi := (70656931963219596363/25000000000000000000)
  directionLo := (17938113400717066383/6250000000000000000)
  directionHi := (287009814411473062129/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree034.table
  base := (-7166374659461537234088729999236943737173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-273430785455828459412940845010587500000000000)
      constant := (2163576917624932952514153554640062604189439243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree034.table
  base := (-898028945405513651820250546286326919693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-411293277096908555556401072642287500000000000)
      constant := (3263858615509448548168378562170148322026302756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17938113400717066383/6250000000000000000)
  centralHi := (287009814411473062129/100000000000000000000)
  directionLo := (145662996833217505159/50000000000000000000)
  directionHi := (291325993666435010319/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree035.table
  base := (-3560500860032452897292654007055355227379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-140741035149059852743576997437140625000000000)
      constant := (1148662074017601943679659692873178296454653489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree035.table
  base := (-7137608173080953214329369529166904925707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-846807885127347665008205701059562500000000000)
      constant := (6931233272096614242081298912389986048099568511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145662996833217505159/50000000000000000000)
  centralHi := (291325993666435010319/100000000000000000000)
  directionLo := (147789576427909195483/50000000000000000000)
  directionHi := (295579152855818390967/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree036.table
  base := (-880341500948662066741987760580516741623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-144766677570205475780683572368987500000000000)
      constant := (1217624809588832660960227387479732687537276772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree036.table
  base := (-882270515327609262710705623721933309061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-145171536010146369817268209472425000000000000)
      constant := (1224557803926130002623884799185540380480180204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147789576427909195483/50000000000000000000)
  centralHi := (295579152855818390967/100000000000000000000)
  directionLo := (149885987187087284759/50000000000000000000)
  directionHi := (299771974374174569519/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree037.table
  base := (-3466580147544394119704166963578071701599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-148792319991351098817790147300834375000000000)
      constant := (1288669162916325714444078393875272072773717509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree037.table
  base := (-6947490921714035642767549954868814916221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-895250546994408772799012812609537500000000000)
      constant := (7776012961850853844696045599573970109797329833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/50000000000000000000)
  centralHi := (299771974374174569519/100000000000000000000)
  directionLo := (60781391111891572537/20000000000000000000)
  directionHi := (151953477779728931343/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree038.table
  base := (-1698431131744024235196466363121247145271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-152817962412496721854896722232681250000000000)
      constant := (1361788369190591481569097356400257906376540322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree038.table
  base := (-6807023220901311428787023491632457544011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-919471877927939326694416368384525000000000000)
      constant := (8217191191098018490080369921722724214655201503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60781391111891572537/20000000000000000000)
  centralHi := (151953477779728931343/50000000000000000000)
  directionLo := (307986426088303147857/100000000000000000000)
  directionHi := (153993213044151573929/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree039.table
  base := (-6625721842349299951590842789433406052157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-313687209667284689784006594329056250000000000)
      constant := (2873952652041486115227636795383475428158379787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree039.table
  base := (-3319027429963115573479300066302948491773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-157282201476911646764969987359918750000000000)
      constant := (1445140831680638889902546182551585342797157843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307986426088303147857/100000000000000000000)
  centralHi := (153993213044151573929/50000000000000000000)
  directionLo := (78003140830944004429/25000000000000000000)
  directionHi := (312012563323776017717/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree040.table
  base := (-1607580700755317480056650572640169740323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-160869247254787967929109872096375000000000000)
      constant := (1514227526498731783203828021879096348326601786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree040.table
  base := (-3220876559497312509239655077659893282569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-483957269897500217242611739967250000000000000)
      constant := (4568470704994964211523519273345237942312924837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78003140830944004429/25000000000000000000)
  centralHi := (312012563323776017717/100000000000000000000)
  directionLo := (315987405902673375641/100000000000000000000)
  directionHi := (157993702951336687821/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree041.table
  base := (-776073008495457728354173840615533173691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-164894889675933590966216447028221875000000000)
      constant := (1593536999572425507485056438037302997576528024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree041.table
  base := (-6219171414001413578925961069475334857361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-992135870728530988380627035709487500000000000)
      constant := (9615450716045837819017927730289279683918771053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315987405902673375641/100000000000000000000)
  centralHi := (157993702951336687821/50000000000000000000)
  directionLo := (19994554112691416649/6250000000000000000)
  directionHi := (63982573160612533277/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree042.table
  base := (-5961459713641357848749720570440986049963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-337841064194158428006646043920137500000000000)
      constant := (3349800513578190384508429228427995957568398133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree042.table
  base := (-5971260634983059927131335207220281517719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-338785733887353847425343530494825000000000000)
      constant := (3368782022492834094479063899738796402449781929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994554112691416649/6250000000000000000)
  centralHi := (63982573160612533277/20000000000000000000)
  directionLo := (323790739094798546589/100000000000000000000)
  directionHi := (32379073909479854659/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree043.table
  base := (-2844905683436172197988591421916909702689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-172946174518224837040429596891915625000000000)
      constant := (1758313244625375620445450065471008039771461699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree043.table
  base := (-2849439647197590131081460346800674564197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-520289266297796048085717073629731250000000000)
      constant := (5304801615528418568926876233083055308295161281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323790739094798546589/100000000000000000000)
  centralHi := (32379073909479854659/10000000000000000000)
  directionLo := (65524543108909481489/20000000000000000000)
  directionHi := (163811357772273703723/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree044.table
  base := (-5394417290953702471753571405994853613711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-353943633878740920155072343647525000000000000)
      constant := (3687544603483171348958061181179532703598593201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree044.table
  base := (-5402802626038385239211025529101093426361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1064799863529122650066837703034450000000000000)
      constant := (11125200324256352545303553207208822810854108053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65524543108909481489/20000000000000000000)
  centralHi := (163811357772273703723/50000000000000000000)
  directionLo := (33141038722105700917/10000000000000000000)
  directionHi := (331410387221057009171/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree045.table
  base := (-2537990272550300396195211522189075916177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-180997459360516083114642746755609375000000000)
      constant := (1931274120595647593129068564753695274743753107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree045.table
  base := (-101674615096702709210131602389192473087/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-181503532410442200660373543134906250000000000)
      constant := (1942186264108477035061236908296949954424360425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/10000000000000000000)
  centralHi := (331410387221057009171/100000000000000000000)
  directionLo := (67031051244997931477/20000000000000000000)
  directionHi := (167577628112494828693/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree046.table
  base := (-2367568160245900860640686885088140023083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-185023101781661706151749321687456250000000000)
      constant := (2020815712930660888856978627348139381929062053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree046.table
  base := (-296393502559355842868585463635570849117/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-556621262698091878928822407292212500000000000)
      constant := (6096668581305004746884266912228258605010795528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67031051244997931477/20000000000000000000)
  centralHi := (167577628112494828693/50000000000000000000)
  directionLo := (169429370824885310091/50000000000000000000)
  directionHi := (338858741649770620183/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree047.table
  base := (-87449170849660180506564961645642997123/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-189048744202807329188855896619303125000000000)
      constant := (2112394378714789653291371145018056970728304825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree047.table
  base := (-2189534844016196048703820667134169920391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-568731928164857155876524185179706250000000000)
      constant := (6372921467384178226034345858071419703625873243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169429370824885310091/50000000000000000000)
  centralHi := (338858741649770620183/100000000000000000000)
  directionLo := (342522185864935632977/100000000000000000000)
  directionHi := (171261092932467816489/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree048.table
  base := (-1994232908580537364500151037942739080617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-193074386623952952225962471551150000000000000)
      constant := (2206007678165698291083130502463628017990474647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree048.table
  base := (-3994567693987778918347221882069642688163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-387228395754414955216150642044800000000000000)
      constant := (4436873445351017139834909611765556731947074333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342522185864935632977/100000000000000000000)
  centralHi := (171261092932467816489/50000000000000000000)
  directionLo := (173073430100435284183/50000000000000000000)
  directionHi := (346146860200870568367/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree049.table
  base := (-1791813395431873191861953915658695616329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-197100029045098575263069046482996875000000000)
      constant := (2301653406536690868876571332232934740172522939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree049.table
  base := (-897314053278655624892878542572407578017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-592953259098387709771927740954693750000000000)
      constant := (6943828104163351528095824830957133220559378282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/50000000000000000000)
  centralHi := (346146860200870568367/100000000000000000000)
  directionLo := (349733970103203664437/100000000000000000000)
  directionHi := (174866985051601832219/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree050.table
  base := (-631672996640578565231127260247146576947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-402251342932488396600351242829687500000000000)
      constant := (4798659142759506699459285592558396622100028385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree050.table
  base := (-3163556390369313961917633378123686599063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1210127849130305973439259037684375000000000000)
      constant := (14476938663930627309961584945832480042118248699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349733970103203664437/100000000000000000000)
  centralHi := (174866985051601832219/50000000000000000000)
  directionLo := (353284659816097981813/100000000000000000000)
  directionHi := (176642329908048990907/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree051.table
  base := (-1356531573608599905134046567522981208321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-205151313887389821337282196346690625000000000)
      constant := (2499034372033215236512780771324790747349970211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree051.table
  base := (-1358924360789264478716067321618048882187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-205724863343972754555777098909893750000000000)
      constant := (2513076160434854101197369429196743531973752517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353284659816097981813/100000000000000000000)
  centralHi := (176642329908048990907/50000000000000000000)
  directionLo := (17840000832301241629/5000000000000000000)
  directionHi := (356800016646024832581/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree052.table
  base := (-449613440864745170776010097215361471319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-418353912617070888748777542557075000000000000)
      constant := (5201532362219539954857813687548754100831797645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree052.table
  base := (-563119246863607093867043492686409696171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-629285255498683540615033074617175000000000000)
      constant := (7846100700232016391217886507700861114512362366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17840000832301241629/5000000000000000000)
  centralHi := (356800016646024832581/100000000000000000000)
  directionLo := (360281074851054477561/100000000000000000000)
  directionHi := (180140537425527238781/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree053.table
  base := (-440922449141720414706945557002632133459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-213202598729681067411495346210384375000000000)
      constant := (2704523527784919642331232263189219024176631038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree053.table
  base := (-883875902038920422322272378663206012393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-641395920965448817562734852504668750000000000)
      constant := (8159081604867619143008115792644171633106932789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360281074851054477561/100000000000000000000)
  centralHi := (180140537425527238781/50000000000000000000)
  directionLo := (72745763839019146191/20000000000000000000)
  directionHi := (90932204798773932739/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree054.table
  base := (-1260213494145976849425817544277358109173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-434456482301653380897203842284462500000000000)
      constant := (5620610165414323158184338654051738282863291243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree054.table
  base := (-252790765596056438457357553082914956541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-435671057621476063006957753594775000000000000)
      constant := (5652111489443608673555891415246346297119528655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72745763839019146191/20000000000000000000)
  centralHi := (90932204798773932739/25000000000000000000)
  directionLo := (367144188201701161267/100000000000000000000)
  directionHi := (91786047050425290317/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree055.table
  base := (-92236711529255981650270775739370436613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-221253883571972313485708496074078125000000000)
      constant := (2918109644369904237838412513316480695849195632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree055.table
  base := (-370668324985247774105047110425178809749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-665617251898979371458138408279656250000000000)
      constant := (8803354009071518797032403797011008458205964977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367144188201701161267/100000000000000000000)
  centralHi := (91786047050425290317/25000000000000000000)
  directionLo := (370528077137905547557/100000000000000000000)
  directionHi := (185264038568952773779/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree056.table
  base := (-3939224551959471492157854129830927337/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-225279525993117936522815071005925000000000000)
      constant := (3027936126801577836763971789151062082617154175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree056.table
  base := (-20012940833255747881063432464288043083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-677727917365744648405840186167150000000000000)
      constant := (9134638695642764188483983466936696457039480795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370528077137905547557/100000000000000000000)
  centralHi := (185264038568952773779/50000000000000000000)
  directionLo := (23367583797186227977/6250000000000000000)
  directionHi := (373881340754979647633/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree057.table
  base := (18118762878711767475334622483230736331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-229305168414263559559921645937771875000000000)
      constant := (3139783548445008879827784868762000915332946290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree057.table
  base := (71892170219282063586903972837809630111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-459892388555006616902361309369762500000000000)
      constant := (6314678914491817978402784484094414324361071995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/6250000000000000000)
  centralHi := (373881340754979647633/100000000000000000000)
  directionLo := (188602397904936992579/50000000000000000000)
  directionHi := (377204795809873985159/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree058.table
  base := (939927179993355065141925348859563330303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-466661621670818365194056441739237500000000000)
      constant := (6507302044220226426817420666534647951687320927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree058.table
  base := (18744940864697229478205829679922567851/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-701949248299275202301243741942137500000000000)
      constant := (9815490396931108729726591437338896154943254425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188602397904936992579/50000000000000000000)
  centralHi := (377204795809873985159/100000000000000000000)
  directionLo := (38049922338842723093/10000000000000000000)
  directionHi := (380499223388427230931/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree059.table
  base := (383881021387994850111596983811118382701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-237356453256554805634134795801465625000000000)
      constant := (3369537745895542545171273186423290462639729918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree059.table
  base := (1533060118191721250641886278547053548763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1428119827532080958497891039659262500000000000)
      constant := (20330104770674543583059527183586399828958433201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38049922338842723093/10000000000000000000)
  centralHi := (380499223388427230931/100000000000000000000)
  directionLo := (383765371049061394849/100000000000000000000)
  directionHi := (7675307420981227897/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree060.table
  base := (2149011905586921158374919666716345847507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-482764191355400857342482741466625000000000000)
      constant := (6974885989970541821893948940919153629329193363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree060.table
  base := (1073373660889555909648747288501171733887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-242056859744268585398882432572375000000000000)
      constant := (3506900727019995179758825147905046587344142783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383765371049061394849/100000000000000000000)
  centralHi := (7675307420981227897/2000000000000000000)
  directionLo := (387003954803631549809/100000000000000000000)
  directionHi := (38700395480363154981/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree061.table
  base := (2780251381108038823519052559992699898111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-490815476197692103416695891330318750000000000)
      constant := (7214732228470758379953150095497661205919451399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree061.table
  base := (2778170624035323051242314718784705019557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1476562489399142066288698151209237500000000000)
      constant := (21764875672026770754132479439736316142024535439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387003954803631549809/100000000000000000000)
  centralHi := (38700395480363154981/10000000000000000000)
  directionLo := (390215660950299139629/100000000000000000000)
  directionHi := (39021566095029913963/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree062.table
  base := (428639579843579251593177743395767234609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-249433380519991674745454520597006250000000000)
      constant := (3729306511474613749716624004210881474547994324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree062.table
  base := (3427205299467472847547761827582334016923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1500783820332672620184101706984225000000000000)
      constant := (22500515179768455026791655675200856386045685521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390215660950299139629/100000000000000000000)
  centralHi := (39021566095029913963/10000000000000000000)
  directionLo := (393401147771719565887/100000000000000000000)
  directionHi := (6146892933933118217/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree063.table
  base := (4095493903780950054395955356925545019169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-506918045882274595565122191057706250000000000)
      constant := (7706527302899535717810611875808892580038486121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree063.table
  base := (2046869322159784434398288429371969227841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-254167525211033862346584210459868750000000000)
      constant := (3874719950676017250127624770461754706121005969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393401147771719565887/100000000000000000000)
  centralHi := (6146892933933118217/1562500000000000000)
  directionLo := (396561047110446610343/100000000000000000000)
  directionHi := (49570130888805826293/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree064.table
  base := (4779280336968840976521826267127932562157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-514969330724565841639335340921400000000000000)
      constant := (7958474100707310137635175188912206717477335213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree064.table
  base := (119441720440178328147703734938816661267/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-774613241099866863987454409267100000000000000)
      constant := (12004143185112123657928489946134559557951672180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396561047110446610343/100000000000000000000)
  centralHi := (49570130888805826293/12500000000000000000)
  directionLo := (399695965832232759357/100000000000000000000)
  directionHi := (199847982916116379679/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree065.table
  base := (2740191491657819238690799224055409461761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-261510307783428543856774245392546875000000000)
      constant := (4107226270879493553427926387123405536102271749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree065.table
  base := (2739451896975766462665047828502959052703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-786723906566632140935156187154593750000000000)
      constant := (12390206290336261903512223173270453318149397581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399695965832232759357/100000000000000000000)
  centralHi := (199847982916116379679/50000000000000000000)
  directionLo := (40280648718682386549/10000000000000000000)
  directionHi := (402806487186823865491/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree066.table
  base := (6198717821923724766798334602732212111029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-531071900409148333787761640648787500000000000)
      constant := (8474461835501940939684869828783896641565171861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree066.table
  base := (6197360417410863297110608383956581472247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-532556381355598278588571976694725000000000000)
      constant := (8521565329386053607560439440750435756322372023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40280648718682386549/10000000000000000000)
  centralHi := (402806487186823865491/100000000000000000000)
  directionLo := (202946586037445096787/50000000000000000000)
  directionHi := (16235726882995607743/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree067.table
  base := (433388056701662647470606890661171622143/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-269561592625719789930987395256240625000000000)
      constant := (4369250633682168230641790660743627031631010396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree067.table
  base := (6932963546553009845193240325050899016793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1621890475000325389661119485859162500000000000)
      constant := (26361134471663954069770110482779904499984516011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202946586037445096787/50000000000000000000)
  centralHi := (16235726882995607743/4000000000000000000)
  directionLo := (408956560228887808913/100000000000000000000)
  directionHi := (204478280114443904457/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree068.table
  base := (3843393796398035061986026237239519535091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-273587235046865412968093970188087500000000000)
      constant := (4503285095725965363602364146939608904930671219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree068.table
  base := (7685645281962196533245074037096018000293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1646111805933855943556523041634150000000000000)
      constant := (27169726114593094438113253567457693675094270511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408956560228887808913/100000000000000000000)
  centralHi := (204478280114443904457/50000000000000000000)
  directionLo := (51499646414361347701/12500000000000000000)
  directionHi := (411997171314890781609/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree069.table
  base := (8456391829776872476000625987944731586213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-555225754936022072010401090239868750000000000)
      constant := (9278668023947044637657281111649218903322803117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree069.table
  base := (8455344268223366871000450967481637754411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-556777712289128832483975532469712500000000000)
      constant := (9330156395022093709386672944106714612443753099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/12500000000000000000)
  centralHi := (411997171314890781609/100000000000000000000)
  directionLo := (83003101192352803563/20000000000000000000)
  directionHi := (51876938245220502227/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree070.table
  base := (2310741383192035666318335392893269867307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-281638519889156659042307120051781250000000000)
      constant := (4777397118571070718693635528665948462519233126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree070.table
  base := (1848401012639696615832925694359999509121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1694554467800917051347330153184125000000000000)
      constant := (28823362118118283747514253576743557124469792335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83003101192352803563/20000000000000000000)
  centralHi := (51876938245220502227/12500000000000000000)
  directionLo := (418012046723448517573/100000000000000000000)
  directionHi := (209006023361724258787/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree071.table
  base := (5023229003331685362910143380375068004141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-285664162310302282079413694983628125000000000)
      constant := (4917474177023481987062443612273849625202525169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree071.table
  base := (10045577568103576109147800434147660623603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1718775798734447605242733708959112500000000000)
      constant := (29668403499610727201841413343494327227359941881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418012046723448517573/100000000000000000000)
  centralHi := (209006023361724258787/50000000000000000000)
  directionLo := (210493629489798353409/50000000000000000000)
  directionHi := (420987258979596706819/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree072.table
  base := (5433411714292938754797732307847963903803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-289689804731447905116520269915475000000000000)
      constant := (5059564971757032786883082414045118054870882427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree072.table
  base := (10866016512522580774580150034666764983569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-580999043222659386379379088244700000000000000)
      constant := (10175197350565192406375279104399442091730400721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210493629489798353409/50000000000000000000)
  centralHi := (420987258979596706819/100000000000000000000)
  directionLo := (6624087371551837159/1562500000000000000)
  directionHi := (423941591779317578177/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree073.table
  base := (2926005094905371381282808006376879516449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-293715447152593528153626844847321875000000000)
      constant := (5203669307916441370146942406964510885342099782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree073.table
  base := (11703280989060311708859704959302056178201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1767218460601508713033540820509087500000000000)
      constant := (31394926619679789902024451613346716600679579627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/1562500000000000000)
  centralHi := (423941591779317578177/100000000000000000000)
  directionLo := (21343773931618154153/5000000000000000000)
  directionHi := (426875478632363083061/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree074.table
  base := (6279005710780091614590483253350360284797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-297741089573739151190733419779168750000000000)
      constant := (5349787009373648737548819855558476762575904973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree074.table
  base := (12557334032848360134580143758436770537613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1791439791535039266928944376284075000000000000)
      constant := (32276406160156024675977408008381165815715202151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21343773931618154153/5000000000000000000)
  centralHi := (426875478632363083061/100000000000000000000)
  directionLo := (53723667281462848399/12500000000000000000)
  directionHi := (429789338251702787193/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree075.table
  base := (6714381357159708865026647569218066630309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-301766731994884774227839994711015625000000000)
      constant := (5497917916927986519009752695920926719588639881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree075.table
  base := (6714071120789797005313854517679531677833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-302610187078094970137391322009843750000000000)
      constant := (5528338288379559687476698078044114779962980697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53723667281462848399/12500000000000000000)
  centralHi := (429789338251702787193/100000000000000000000)
  directionLo := (216341787625544105229/50000000000000000000)
  directionHi := (432683575251088210459/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree076.table
  base := (1789530458767252649932694477075051234563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-305792374416030397264946569642862500000000000)
      constant := (5648061886679332300481566326183059518889013068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree076.table
  base := (55920607156891249677200924859170140217/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-919941226701050187359875743917025000000000000)
      constant := (17037898239032856478098321977715978517631873152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216341787625544105229/50000000000000000000)
  centralHi := (432683575251088210459/100000000000000000000)
  directionLo := (217779290400448565969/50000000000000000000)
  directionHi := (435558580800897131939/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree077.table
  base := (3044085328201199974201858633325541132419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-619636033674352040604106289149418750000000000)
      constant := (11600437577115246132580497244070460287652776855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree077.table
  base := (15219906330476766443573767631820622153571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1864103784335630928615155043609037500000000000)
      constant := (34993705633654354569322449331172374724966348617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/50000000000000000000)
  centralHi := (435558580800897131939/100000000000000000000)
  directionLo := (219207366622633805357/50000000000000000000)
  directionHi := (87682946649053522143/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree078.table
  base := (16141286636135384635365178837142740852361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-627687318516643286678319439013112500000000000)
      constant := (11908777009987393631521900698496787181492364649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree078.table
  base := (4035202572751374156473263227348105574251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-314720852544860247085093099897337500000000000)
      constant := (5987292750229069680685447071465987041321255318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219207366622633805357/50000000000000000000)
  centralHi := (87682946649053522143/20000000000000000000)
  directionLo := (110313099670819545961/25000000000000000000)
  directionHi := (88250479736655636769/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree079.table
  base := (17078801066584568786523218769947823464243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-635738603358934532752532588876806250000000000)
      constant := (12221141859435755520290532617551517635428187387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree079.table
  base := (341567300870399702850781641997652961337/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-956273223101346018202981077579506250000000000)
      constant := (18432974226302055489314698396304990921460237475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110313099670819545961/25000000000000000000)
  centralHi := (88250479736655636769/20000000000000000000)
  directionLo := (111017982879175423769/25000000000000000000)
  directionHi := (444071931516701695077/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree080.table
  base := (9016474757213103576582569243393128652333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-321894944100612889413372869370250000000000000)
      constant := (6268765966674026704084729678334367197489801197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree080.table
  base := (9016275232077345656215782926560186935097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-968383888568111295150682855467000000000000000)
      constant := (18910140459653540318033869547563639396616983019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111017982879175423769/25000000000000000000)
  centralHi := (444071931516701695077/100000000000000000000)
  directionLo := (223436837483326438257/50000000000000000000)
  directionHi := (89374734993330575303/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree081.table
  base := (19003713524099678127761328042282276867753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-651841173043517024900958888604193750000000000)
      constant := (12857947058075917406453434815872396882501812977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree081.table
  base := (3800669673710815276803485615305282583861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-653663036023251048065589755569662500000000000)
      constant := (12928917796064507754695873552494193464470240745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/50000000000000000000)
  centralHi := (89374734993330575303/20000000000000000000)
  directionLo := (449657961561261854277/100000000000000000000)
  directionHi := (224828980780630927139/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree082.table
  base := (9995538206907947119068395278085085194033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-329946228942904135487586019233943750000000000)
      constant := (6591193538330196995558382224758042507996906497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree082.table
  base := (19990742324953347397257119770903595330221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-1985210439003283698092172822483975000000000000)
      constant := (39765365395444014051806005130075548129136148167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449657961561261854277/100000000000000000000)
  centralHi := (224828980780630927139/50000000000000000000)
  directionLo := (90485022719267030043/20000000000000000000)
  directionHi := (56553139199541893777/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree083.table
  base := (524875577627180391286003238338080712871/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-333971871364049758524692594165790625000000000)
      constant := (6755425923613996479486074733989516693587127280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree083.table
  base := (4198943497054680345715478746077559859131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2009431769936814251987576378258962500000000000)
      constant := (40756116521941824169467290464026255434155953685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90485022719267030043/20000000000000000000)
  centralHi := (56553139199541893777/12500000000000000000)
  directionLo := (455175443570810711547/100000000000000000000)
  directionHi := (113793860892702677887/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree084.table
  base := (2751942496080059552005186709676925832411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-337997513785195381561799169097637500000000000)
      constant := (6921670620770441545790352300204232421253620396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree084.table
  base := (22015260432493810360108493136462445004713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-677884366956781601960993311344650000000000000)
      constant := (13919668796321572655728022344539478270049344617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455175443570810711547/100000000000000000000)
  centralHi := (113793860892702677887/25000000000000000000)
  directionLo := (457909254598672429849/100000000000000000000)
  directionHi := (9158185091973448597/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree085.table
  base := (23052614685138573907307342947629272233603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-684046312412682009197811488058968750000000000)
      constant := (14179855143686421590347252868565973558774095627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree085.table
  base := (2305235904273502288651266546242811109217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1028937215901937679889191744904468750000000000)
      constant := (21387017327145973687832433049140470845118091295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457909254598672429849/100000000000000000000)
  centralHi := (9158185091973448597/2000000000000000000)
  directionLo := (460626840798861100589/100000000000000000000)
  directionHi := (46062684079886110059/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree086.table
  base := (6026559029821853221108053252249917976149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-346048798627486627636012318961331250000000000)
      constant := (7260196724446313156575527829260995304131421882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree086.table
  base := (12053001180316093610586475547016779687923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1041047881368702956836893522791962500000000000)
      constant := (21900600504343214357530375369491153187126002521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460626840798861100589/100000000000000000000)
  centralHi := (46062684079886110059/10000000000000000000)
  directionLo := (231664243832300785903/50000000000000000000)
  directionHi := (463328487664601571807/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree087.table
  base := (5035278841208357241947201590563102270649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-700148882097264501346237787786356250000000000)
      constant := (14864956062457486906033680947871453304525807205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree087.table
  base := (25176180486719608928121000255788600248987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-702105697890312155856396867119637500000000000)
      constant := (14946835057571981276175880782203255760055218683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231664243832300785903/50000000000000000000)
  centralHi := (463328487664601571807/100000000000000000000)
  directionLo := (116503618103364705227/25000000000000000000)
  directionHi := (466014472413458820909/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree088.table
  base := (2626307984774741456382482831444640650109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-354100083469777873710225468825025000000000000)
      constant := (7606771449390587127439475768275827181884377905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree088.table
  base := (13131442237834167757887868607763777250229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1065269212302233510732297078566950000000000000)
      constant := (22945973446940346187042840948235741890442213983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116503618103364705227/25000000000000000000)
  centralHi := (466014472413458820909/100000000000000000000)
  directionLo := (234342532159668944469/50000000000000000000)
  directionHi := (468685064319337888939/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree089.table
  base := (6841571205292030594500820083028717650661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-358125725890923496747332043756871875000000000)
      constant := (7783076940245629591880506232329014706601701198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree089.table
  base := (27366106244330910364161280781082608959199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2154759755537997575359997712908887500000000000)
      constant := (46955525944017671093722810190156135014028810173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/50000000000000000000)
  centralHi := (468685064319337888939/100000000000000000000)
  directionLo := (47134052502755310553/10000000000000000000)
  directionHi := (471340525027553105531/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree090.table
  base := (28486001693448139785467580259688473167789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-724302736624138239568877237377437500000000000)
      constant := (15922788937652001754003106930923218414348226701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree090.table
  base := (5697167697729629392347489449421808011169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-726327028823842709751800422894625000000000000)
      constant := (16010414038985067109925927487404318489135445605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47134052502755310553/10000000000000000000)
  centralHi := (471340525027553105531/100000000000000000000)
  directionLo := (236990554427005031731/50000000000000000000)
  directionHi := (473981108854010063463/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree091.table
  base := (7405555936537705916505939366314344323917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-366177010733214742821545193620565625000000000)
      constant := (8141724003524815795243664932835790855901532606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree091.table
  base := (29622074608563863714705519460361989054611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2203202417405058683150804824458862500000000000)
      constant := (49119095226393497244402442323557302513482004697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236990554427005031731/50000000000000000000)
  centralHi := (473981108854010063463/100000000000000000000)
  directionLo := (119151765767367160139/25000000000000000000)
  directionHi := (476607063069468640557/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree092.table
  base := (30774944906597618382051190895622804115923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-740405306308720731717303537104825000000000000)
      constant := (16648131031546316163219308845413571995176719507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree092.table
  base := (1923425540010989348995300367378439560153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1113711874169294618523104190116925000000000000)
      constant := (25109542551994745281027482737005471895215509848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119151765767367160139/25000000000000000000)
  centralHi := (476607063069468640557/100000000000000000000)
  directionLo := (479218628169786384003/100000000000000000000)
  directionHi := (119804657042446596001/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree093.table
  base := (15972079842902836145344742444909266781681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-374228295575505988895758343484259375000000000)
      constant := (8508418979748107910545685203687579049937899029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree093.table
  base := (15972017597212773812219524580036255256213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-375274179878686631823601989334806250000000000)
      constant := (8555201932937704514911678606272405754611958117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479218628169786384003/100000000000000000000)
  centralHi := (119804657042446596001/25000000000000000000)
  directionLo := (481816038132978198541/100000000000000000000)
  directionHi := (240908019066489099271/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree094.table
  base := (33129863122389952108422648625036725475361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-756507875993303223865729836832212500000000000)
      constant := (17389568744217658785938912593904541057810171649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree094.table
  base := (33129749401696711914585242539468638253327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2275866410205650344837015491783825000000000000)
      constant := (52455474569849047359396979122417196095726661229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481816038132978198541/100000000000000000000)
  centralHi := (240908019066489099271/50000000000000000000)
  directionLo := (15137485020745937627/3125000000000000000)
  directionHi := (96879904132774000813/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree095.table
  base := (17166025365928321444849280327796806629929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-382279580417797234969971493347953125000000000)
      constant := (8883161671758021376469617747159641154557564461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree095.table
  base := (4291493357719113045672580925930152331899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1150043870569590449366209523779406250000000000)
      constant := (26795936948226238999218986082824284432458802292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15137485020745937627/3125000000000000000)
  centralHi := (96879904132774000813/20000000000000000000)
  directionLo := (486969297427070390233/100000000000000000000)
  directionHi := (243484648713535195117/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree096.table
  base := (2221919903798106854310114357069264613547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-386305222838942858007078068279800000000000000)
      constant := (9073550859626294034550714216087592685990909784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree096.table
  base := (35550623598499975856962864793344609159879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-774769690690903817542607534444600000000000000)
      constant := (18246803155067769819795564943861379427585301511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486969297427070390233/100000000000000000000)
  centralHi := (243484648713535195117/50000000000000000000)
  directionLo := (48952558426893488169/10000000000000000000)
  directionHi := (489525584268934881691/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree097.table
  base := (9196465661330572678565741686319401663277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (445205157323319902773484100000000000000)
      linear := (-41484840605812358491251423446875000000000)
      constant := (984796675361597192708554504462702279889054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree097.table
  base := (9196444004777036303361355143234459765661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (81)
      square := (1335615471969959708320452300000000000000)
      linear := (-124802338346595919147796054793750000000000)
      constant := (2970617556312399591295111043422199727343966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/10000000000000000000)
  centralHi := (489525584268934881691/100000000000000000000)
  directionLo := (492068591429151864363/100000000000000000000)
  directionHi := (123017147857287966091/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree098.table
  base := (4754684996736200090764499177244361204519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-394356507681234104081291218143493750000000000)
      constant := (9460364832731404428960411311292566532199527084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree098.table
  base := (7607480175414731892697520347034402282101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2372751733939772560418629714883775000000000000)
      constant := (57073888933263694712130052210090140209834324635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492068591429151864363/100000000000000000000)
  centralHi := (123017147857287966091/25000000000000000000)
  directionLo := (494598523742537174539/100000000000000000000)
  directionHi := (24729926187126858727/5000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree099.table
  base := (39305567453180705139534648818117861955003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-796764300204759454236795586150681250000000000)
      constant := (19313579176613532322373204576062563980712748227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree099.table
  base := (19652747619420175129678081465454721740139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-399495510812217185719005545109793750000000000)
      constant := (9709805443021449517475197716671264355759217851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494598523742537174539/100000000000000000000)
  centralHi := (24729926187126858727/5000000000000000000)
  directionLo := (124278895207896378439/25000000000000000000)
  directionHi := (497115580831585513757/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree100.table
  base := (40590122377643299685456134227630034748093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-804815585047050700311008736014375000000000000)
      constant := (19710452344950164734879112652272478028194807037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree100.table
  base := (253687852835237565355480687281781202183/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1210597197903416834104718413216875000000000000)
      constant := (29727956137229226025048098452693594227021563280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124278895207896378439/25000000000000000000)
  centralHi := (497115580831585513757/100000000000000000000)
  directionLo := (124904989322572737299/25000000000000000000)
  directionHi := (499619957290290949197/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree101.table
  base := (41891142301808868311747004368000109332311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-812866869889341946385221885878068750000000000)
      constant := (20111349147463292827904023264589550577535839199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree101.table
  base := (20945541063113788893135813112924980318411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1222707863370182111052420191104368750000000000)
      constant := (30332563857321273268588027152933146993666537297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124904989322572737299/25000000000000000000)
  centralHi := (499619957290290949197/100000000000000000000)
  directionLo := (502111842859715542197/100000000000000000000)
  directionHi := (251055921429857771099/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree102.table
  base := (43208625015295637105184741086132083520683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-820918154731633192459435035741762500000000000)
      constant := (20516269563355434490698425739711301344158606347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree102.table
  base := (43208570092272989111646181081752415361803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-823212352557964925333414645994575000000000000)
      constant := (20628826305862755503984624958710303007389204427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502111842859715542197/100000000000000000000)
  centralHi := (251055921429857771099/50000000000000000000)
  directionLo := (252295711297877195623/50000000000000000000)
  directionHi := (504591422595754391247/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree103.table
  base := (44542568520213898998842000382132609413867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-828969439573924438533648185605456250000000000)
      constant := (20925213573828445469469600697942733817678199603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree103.table
  base := (44542518396086566070937068347028256873819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2493858388607425329895647493758712500000000000)
      constant := (63119965828092415877303692027075470317714788913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252295711297877195623/50000000000000000000)
  centralHi := (504591422595754391247/100000000000000000000)
  directionLo := (63382359628689609471/12500000000000000000)
  directionHi := (507058877029516875769/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree104.table
  base := (9178594202148566258171346919812074295473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-837020724416215684607861335469150000000000000)
      constant := (21338181161891357643415728132879687160230527285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree104.table
  base := (45892925270519188396589323097407176496229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2518079719540955883791051049533700000000000000)
      constant := (64365588396273676415433231763782599870959055983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63382359628689609471/12500000000000000000)
  centralHi := (507058877029516875769/100000000000000000000)
  directionLo := (127378595580179364343/25000000000000000000)
  directionHi := (509514382320717457373/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree105.table
  base := (5907478856833764520786503275619931816793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-422536004629253465341037242666421875000000000)
      constant := (10877586156093342657108033293731994082958383848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree105.table
  base := (9451957823757711136750743239486912815617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-847433683491495479228818201769562500000000000)
      constant := (21874448859019891377604938298481940133723201765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127378595580179364343/25000000000000000000)
  centralHi := (509514382320717457373/100000000000000000000)
  directionLo := (255979055202222433609/50000000000000000000)
  directionHi := (511958110404444867219/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree106.table
  base := (12160786644176432555556988986018883998161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-426561647050399088378143817598268750000000000)
      constant := (11088093505416712325836271270709122206733643698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree106.table
  base := (48643108498058758374602543321362208610397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2566522381408016991581858161083675000000000000)
      constant := (66893240329723479810359638812062237156195676119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255979055202222433609/50000000000000000000)
  centralHi := (511958110404444867219/100000000000000000000)
  directionLo := (257195114565827864077/50000000000000000000)
  directionHi := (102878045826331145631/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree107.table
  base := (12510729210849849344046923352818861389203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-430587289471544711415250392530115625000000000)
      constant := (11300612622642571004062565748730278951786084554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree107.table
  base := (25021441052301189502413868165950569233701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1295371856170773772738630858429331250000000000)
      constant := (34087634808732389817651339837160297166978428127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257195114565827864077/50000000000000000000)
  centralHi := (102878045826331145631/20000000000000000000)
  directionLo := (258405451201858744209/50000000000000000000)
  directionHi := (516810902403717488419/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree108.table
  base := (51459140449507585723011475185520339990067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-869225863785380668904713934923925000000000000)
      constant := (23030287004201700991878185241562374160216540403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree108.table
  base := (25729554380196305159905031170768801749801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-435827507212513016562110878772275000000000000)
      constant := (11578239067838568486544633399250840218163877609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258405451201858744209/50000000000000000000)
  centralHi := (516810902403717488419/100000000000000000000)
  directionLo := (10384405806026117051/2000000000000000000)
  directionHi := (519220290301305852551/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree109.table
  base := (5289181630567074032668832159339503849239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-438638574313835957489463542393809375000000000)
      constant := (11731686138666658775269388232988264873626511255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree109.table
  base := (13222946850246893722869934135355376118781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1319593187104304326634034414204318750000000000)
      constant := (35387867334188686394046437579908083165128412574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10384405806026117051/2000000000000000000)
  centralHi := (519220290301305852551/100000000000000000000)
  directionLo := (521618549207943568403/100000000000000000000)
  directionHi := (130404637301985892101/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree110.table
  base := (54340943427274831931633322530901079578529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-885328433469963161053140234651312500000000000)
      constant := (23900481055415758282841106751534503140566879361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree110.table
  base := (54340917064582312419031033099270046734911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2663407705142139207163472384183625000000000000)
      constant := (72094170374353796627367060744186122952936332797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521618549207943568403/100000000000000000000)
  centralHi := (130404637301985892101/25000000000000000000)
  directionLo := (131001457982112590163/25000000000000000000)
  directionHi := (524005831928450360653/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree111.table
  base := (27903260462191701474040424038927193592591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-446689859156127203563676692257503125000000000)
      constant := (12170806665037805529661535643158641184239251219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree111.table
  base := (5580649688211590248511518844353992816823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-447938172679278293509812656659768750000000000)
      constant := (12237456916738283306078308933213493064723688035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131001457982112590163/25000000000000000000)
  centralHi := (524005831928450360653/100000000000000000000)
  directionLo := (526382287802557893909/100000000000000000000)
  directionHi := (52638228780255789391/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree112.table
  base := (57288547992637230457587409496610236721229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-901431003154545653201566534378700000000000000)
      constant := (24786769093744659951545035284792368217310043661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree112.table
  base := (57288526068332035515984957565950700149149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2711850367009200314954279495733600000000000000)
      constant := (74767448024439652565063090240251940413110028823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526382287802557893909/100000000000000000000)
  centralHi := (52638228780255789391/10000000000000000000)
  directionLo := (52874806281392881379/10000000000000000000)
  directionHi := (528748062813928813791/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree113.table
  base := (5878702390502861316286595094447737078031/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-454741143998418449637889842121196875000000000)
      constant := (12617974169791244749000412419267939323062530895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree113.table
  base := (5878700391370114452362768980563061029609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1368035848971365434424841525754293750000000000)
      constant := (38061144963177881862888068788447321036382616215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52874806281392881379/10000000000000000000)
  centralHi := (528748062813928813791/100000000000000000000)
  directionLo := (531103299694805070771/100000000000000000000)
  directionHi := (132775824923701267693/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree114.table
  base := (30150974002233113097980418079841789338151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-458766786419564072674996417053043750000000000)
      constant := (12844575530703263711503922682980399462288912759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree114.table
  base := (15075482444280266403119281217290017755253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-460048838146043570457514434547262500000000000)
      constant := (12914877864680273756388141129984451444743350954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531103299694805070771/100000000000000000000)
  centralHi := (132775824923701267693/25000000000000000000)
  directionLo := (533448138026497805023/100000000000000000000)
  directionHi := (16670254313328056407/3125000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree115.table
  base := (30916659848527282907977863079414922079071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-462792428840709695712102991984890625000000000)
      constant := (13073188626814405465933907516786163854381041539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree115.table
  base := (3091665153966059861416114678577107042257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1392257179904895988320245081529281250000000000)
      constant := (39434189896633108866325252411051615766536633390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533448138026497805023/100000000000000000000)
  centralHi := (16670254313328056407/3125000000000000000)
  directionLo := (535782714335918992443/100000000000000000000)
  directionHi := (133945678583979748111/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree116.table
  base := (63381138446019307812074609235059670706667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-933636142523710637498419133833475000000000000)
      constant := (26607626911198830408081542347220652222929029803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree116.table
  base := (31690561648451179478355199694704040946161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1404367845371661265267946859416775000000000000)
      constant := (40129813863567750321591176308009540651287286547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535782714335918992443/100000000000000000000)
  centralHi := (133945678583979748111/25000000000000000000)
  directionLo := (10762143243766875203/2000000000000000000)
  directionHi := (538107162188343760151/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree117.table
  base := (2029543867694265733997664713140877574191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-470843713683000941786316141848584375000000000)
      constant := (13536450014775933219182336480018365454193072404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree117.table
  base := (12989077991390216932130843126621941138469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-944319007225617694810432424869512500000000000)
      constant := (27221003658780187620425217237961852853671774105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10762143243766875203/2000000000000000000)
  centralHi := (538107162188343760151/100000000000000000000)
  directionLo := (270210806138290858171/50000000000000000000)
  directionHi := (540421612276581716343/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree118.table
  base := (6652611521916950287546021003362549820681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-474869356104146564823422716780431250000000000)
      constant := (13771098302281146111583923968113031878970187645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree118.table
  base := (16631525658043247259711573136850604002503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1428589176305191819163350415191762500000000000)
      constant := (41539264764410082886515198365730687045232304362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270210806138290858171/50000000000000000000)
  centralHi := (540421612276581716343/100000000000000000000)
  directionLo := (271363096253362875903/50000000000000000000)
  directionHi := (542726192506725751807/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree119.table
  base := (68123272408582887269755180704764974128139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-957789997050584375721058583424556250000000000)
      constant := (28015516632501364167896435043578442674774784851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree119.table
  base := (68123260936495181969984890396532954121789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2881399683543914192222104386158512500000000000)
      constant := (84506183373676629908992603461225420656933238103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271363096253362875903/50000000000000000000)
  centralHi := (542726192506725751807/100000000000000000000)
  directionLo := (545021028080637509921/100000000000000000000)
  directionHi := (272510514040318754961/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree120.table
  base := (1089638671504493240415350757018385837911/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-482920640946437810897635866644125000000000000)
      constant := (14246430054999534655737567764633878317664947168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree120.table
  base := (2789474580843701044886512591006372845053/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-968540338159148248705835980644500000000000000)
      constant := (28648657500354556039231509175566036552477591925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545021028080637509921/100000000000000000000)
  centralHi := (272510514040318754961/50000000000000000000)
  directionLo := (109461248315064008799/20000000000000000000)
  directionHi := (136826560393830010999/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree121.table
  base := (2230216331205487788359681936439869758601/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-486946283367583433934742441575971875000000000)
      constant := (14487113517004819851456350452672460613290391444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree121.table
  base := (35683456535398444899946781575646092359153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1464921172705487650006455748854243750000000000)
      constant := (43698948451042514772883835710454489104490561731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109461248315064008799/20000000000000000000)
  centralHi := (136826560393830010999/25000000000000000000)
  directionLo := (137395488254830011029/25000000000000000000)
  directionHi := (549581953019320044117/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree122.table
  base := (73013414982887332109163712240108595365581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-981943851577458113943698033015637500000000000)
      constant := (29459617401780381306659269072764472594107251629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree122.table
  base := (73013406300852483651267737783623845693223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (3048516)
      previous := (1524258)
      next := (1524258)
      square := (25133611951530701791174271381400000000000000)
      linear := (-2954063676344505853908315053483475000000000000)
      constant := (88861956568702912527175688573814133886132605621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137395488254830011029/25000000000000000000)
  centralHi := (549581953019320044117/100000000000000000000)
  directionLo := (275924139983147191143/50000000000000000000)
  directionHi := (551848279966294382287/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree123.table
  base := (74676351864816822965354147704138975602787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-989995136419749360017911182879331250000000000)
      constant := (29949031210823498886675058589051228045274747883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree123.table
  base := (37338171976991963562426504640850685412469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-496380834546339401300619768209743750000000000)
      constant := (15056358582275867482515549770618210290452170821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275924139983147191143/50000000000000000000)
  centralHi := (551848279966294382287/100000000000000000000)
  directionLo := (138526334391467139911/25000000000000000000)
  directionHi := (110821067513173711929/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree124.table
  base := (76355733005405264743460915930242956114363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-998046421262040606092124332743025000000000000)
      constant := (30442468458890628933311965875470850505330041467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree124.table
  base := (38177862898873452505959824450564505257499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1501253169105783480849561082516725000000000000)
      constant := (45913240835190350482061843758663151477403424273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138526334391467139911/25000000000000000000)
  centralHi := (110821067513173711929/20000000000000000000)
  directionLo := (111270647726381582113/20000000000000000000)
  directionHi := (278176619315953955283/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree125.table
  base := (39025779094347208867806197407206630717947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-503048853052165926083168741303359375000000000)
      constant := (15469964571974910184579313419823367759714225823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree125.table
  base := (19512887905533544768138424395417417482923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1513363834572548757797262860404218750000000000)
      constant := (46663473546475763210234401966135972523299685042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111270647726381582113/20000000000000000000)
  centralHi := (278176619315953955283/50000000000000000000)
  directionLo := (558592093708316095643/100000000000000000000)
  directionHi := (139648023427079023911/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree126.table
  base := (9970478402439406382691906115587546252809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-507074495473311549120275316235206250000000000)
      constant := (15720706632082363891331274834249835019676969524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree126.table
  base := (79763821237412344478451366994812190728657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-1016983000026209356496643092194475000000000000)
      constant := (31613182585337358815346705611799101183815933713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558592093708316095643/100000000000000000000)
  centralHi := (139648023427079023911/25000000000000000000)
  directionLo := (70102751391558683931/12500000000000000000)
  directionHi := (560822011132469471449/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree127.table
  base := (4074626996074456220816957356921120523713/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-511100137894457172157381891167053125000000000)
      constant := (15973460408937902273597510618248170168552718670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree127.table
  base := (40746267236083546293913398894230513659563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1537585165506079311692666416179206250000000000)
      constant := (48182141827361919675402968387385388752037234801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70102751391558683931/12500000000000000000)
  centralHi := (560822011132469471449/100000000000000000000)
  directionLo := (563043097096390333933/100000000000000000000)
  directionHi := (281521548548195166967/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree128.table
  base := (41618848067610546082666327216385637784233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-515125780315602795194488466098900000000000000)
      constant := (16228225901791651809639614915753572465911848297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree128.table
  base := (10404711396442110597031068529417521796911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (1524258)
      previous := (762129)
      next := (762129)
      square := (12566805975765350895587135690700000000000000)
      linear := (-1549695830972844588640368194066700000000000000)
      constant := (48950577392357769242007218722378273551045627188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell044.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563043097096390333933/100000000000000000000)
  centralHi := (281521548548195166967/50000000000000000000)
  directionLo := (282627727852878385451/50000000000000000000)
  directionHi := (565255455705756770903/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree129.table
  base := (1062491196458335813776252215950368699621/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (508086)
      previous := (254043)
      next := (254043)
      square := (4188935325255116965195711896900000000000000)
      linear := (-519151422736748418231595041030746875000000000)
      constant := (16485003109965956140886005566996077077265922060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree129.table
  base := (84999291195616878709414802453412350019841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1016172)
      previous := (508086)
      next := (508086)
      square := (8377870650510233930391423793800000000000000)
      linear := (-1041204330959739910392046647969462500000000000)
      constant := (33150053714012693287031760496150781996649183969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell044.Kernel129
