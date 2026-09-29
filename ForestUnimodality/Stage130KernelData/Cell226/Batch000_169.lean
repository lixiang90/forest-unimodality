import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell226.Parameters
import ForestUnimodality.BinomialMassData.Q7_12.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_12.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_12.Batch100_149
import ForestUnimodality.BinomialMassData.Q7_12.Batch150_199
import ForestUnimodality.BinomialMassData.Q53_90.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_90.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_90.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_90.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree000.table
  base := (1816317757593635622392014281/100000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-3964158445451904377865304200000000000000)
      constant := (544895327278090686717604284300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree000.table
  base := (1816317757593635622392014281/100000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-29731188340889282833989781500000000000000)
      constant := (4086714954585680150382032132250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree001.table
  base := (19855530485786853658882035246924135802469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-15885325303956210306333129900000000000000)
      constant := (901600730380499392319670890174086111111105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree001.table
  base := (24624643522201412003624948110946836419753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-358275430046357695572367683600000000000000)
      constant := (20130241112044594532809255819901937499999930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49203532945521174783/100000000000000000000)
  directionHi := (192201300568442089/390625000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree002.table
  base := (58642514247297000059811299715441068672839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-19878175271556707479070347200000000000000)
      constant := (546315507746955245895690348988969618055551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree002.table
  base := (14470675456735420757617202096020163001543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-448970165024711845638827333700000000000000)
      constant := (12143215959788067655121833414016332031249830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49203532945521174783/100000000000000000000)
  centralHi := (192201300568442089/390625000000000000)
  directionLo := (69584303608227447063/100000000000000000000)
  directionHi := (8698037951028430883/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree003.table
  base := (7523670106962420669781677171690310783999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-7957008413052401550602521500000000000000)
      constant := (123286072605627577734134505062854661759985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree003.table
  base := (18518967486555383520096129574920620034843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-59962766667007332856142998200000000000000)
      constant := (912583197151967602263943119606427901567935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/100000000000000000000)
  centralHi := (8698037951028430883/12500000000000000000)
  directionLo := (42611509486765905237/50000000000000000000)
  directionHi := (3408920758941272419/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree004.table
  base := (25975744979598723178601037688021214771239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-27863875206757701824544781800000000000000)
      constant := (280164113783354159391906815992190932941151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree004.table
  base := (1022260527194574098409212386760458178969/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-1260719269962840291543493267800000000000000)
      constant := (12465536170850371885847306410269639062061125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/50000000000000000000)
  centralHi := (3408920758941272419/4000000000000000000)
  directionLo := (98407065891042349567/100000000000000000000)
  directionHi := (192201300568442089/195312500000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree005.table
  base := (9474221210455357157426055751591023354649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-31856725174358198997281999100000000000000)
      constant := (234336899199654217357865958091138420383682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree005.table
  base := (18641476080610636207092052587053319229557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-1442108739919548591676412568000000000000000)
      constant := (10460778837451320196718840121506594287970585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98407065891042349567/100000000000000000000)
  centralHi := (192201300568442089/195312500000000000)
  directionLo := (55011222199667901651/50000000000000000000)
  directionHi := (110022444399335803303/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree006.table
  base := (1787291058818997297038593404396793195759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-11949858380652898723339738800000000000000)
      constant := (70744514857339340556035066955523036698216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree006.table
  base := (878959825384120883948730481563205976307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-90194344993125382878296214900000000000000)
      constant := (528293979361709427646581567002754151470520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55011222199667901651/50000000000000000000)
  centralHi := (110022444399335803303/100000000000000000000)
  directionLo := (120523549258748291833/100000000000000000000)
  directionHi := (60261774629374145917/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree007.table
  base := (10952614792032061130072977226671048479617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-39842425109559193342756433700000000000000)
      constant := (204198954872031484226542835402539436316553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree007.table
  base := (10763363439861911865153884277360986102573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-1804887679832965191942251168400000000000000)
      constant := (9182263331802344955253761711961199371542065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120523549258748291833/100000000000000000000)
  centralHi := (60261774629374145917/50000000000000000000)
  directionLo := (13018031179962242501/10000000000000000000)
  directionHi := (130180311799622425011/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree008.table
  base := (8381849152969929065468982889640032006201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-43835275077159690515493651000000000000000)
      constant := (205468060008265303437096494406760288055809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree008.table
  base := (8222819354796436486897306931632390289077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-1986277149789673492075170468600000000000000)
      constant := (9269630399406382150687199813391118067076185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13018031179962242501/10000000000000000000)
  centralHi := (130180311799622425011/100000000000000000000)
  directionLo := (69584303608227447063/50000000000000000000)
  directionHi := (139168607216454894127/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree009.table
  base := (1578200378163455528122780545441323536489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-15942708348253395896076956100000000000000)
      constant := (71193929871437879556571799832795882437868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree009.table
  base := (6175282099986063807895447194669482737547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-240851846638486865800898863200000000000000)
      constant := (1073720386298076264747822953190126723189615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/50000000000000000000)
  centralHi := (139168607216454894127/100000000000000000000)
  directionLo := (147610598836563524351/100000000000000000000)
  directionHi := (576603901705326267/390625000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree010.table
  base := (4595363112281883449887533833362302176277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-51820975012360684860968085600000000000000)
      constant := (227189164860959778533132799250260719586493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree010.table
  base := (4474502283418634888701035442341886003609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-2349056089703090092341009069000000000000000)
      constant := (10304591559866333280907237810148463831461645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147610598836563524351/100000000000000000000)
  centralHi := (576603901705326267/390625000000000000)
  directionLo := (31119046606996093217/20000000000000000000)
  directionHi := (77797616517490233043/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree011.table
  base := (196274833335531743181778838465437374571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-55813824979961182033705302900000000000000)
      constant := (245487956181833276346600885801522981938224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree011.table
  base := (303339320909573105615149186612047992199/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-1265222779829899196236964184600000000000000)
      constant := (5578842268538981641293424342624397184202975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31119046606996093217/20000000000000000000)
  centralHi := (77797616517490233043/50000000000000000000)
  directionLo := (81594828570092087971/50000000000000000000)
  directionHi := (163189657140184175943/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree012.table
  base := (1890373737482891491850775462668993123871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-19935558315853893068814173400000000000000)
      constant := (89320129877018965538930497988006979371613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree012.table
  base := (448864107746918962677691392921594467631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-150657501645361482922602648300000000000000)
      constant := (677771140981975412314285477322943502086790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81594828570092087971/50000000000000000000)
  centralHi := (163189657140184175943/100000000000000000000)
  directionLo := (42611509486765905237/25000000000000000000)
  directionHi := (170446037947063620949/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree013.table
  base := (805220223661261289206408849466348564711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-63799524915162176379179737500000000000000)
      constant := (294245816299956682672132019607697137082399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree013.table
  base := (721117205396361427538270310443890012367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-2893224499573214992739766969600000000000000)
      constant := (13415151790461382020957670099159775455008635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/25000000000000000000)
  centralHi := (170446037947063620949/100000000000000000000)
  directionLo := (177405860969058289751/100000000000000000000)
  directionHi := (22175732621132286219/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree014.table
  base := (-4522104665004594676929392451641963291/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-67792374882762673551916954800000000000000)
      constant := (324077438917878755698888543523927114572192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree014.table
  base := (-219034476525017820383455240749610579719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-3074613969529923292872686269800000000000000)
      constant := (14791587241852480809646371371416407715213805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177405860969058289751/100000000000000000000)
  centralHi := (22175732621132286219/12500000000000000000)
  directionLo := (11506422656311518107/6250000000000000000)
  directionHi := (184102762500984289713/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree015.table
  base := (-245571412623514992684228921739719866697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-23928408283454390241551390700000000000000)
      constant := (119083122487482859047737293126623361599636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree015.table
  base := (-130970136613955496709190677237389223979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-180889079971479532944755865000000000000000)
      constant := (906664893789116946948472283472269939683780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11506422656311518107/6250000000000000000)
  centralHi := (184102762500984289713/100000000000000000000)
  directionLo := (190564463672571478771/100000000000000000000)
  directionHi := (47641115918142869693/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree016.table
  base := (-862828294255520968891632659942509401923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-75778074817963667897391389400000000000000)
      constant := (393598324756891067371224688121034830765386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree016.table
  base := (-1783138961678005307980113624680880872601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-3437392909443339893138524870200000000000000)
      constant := (17992973420760886975598549063924243246596595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190564463672571478771/100000000000000000000)
  centralHi := (47641115918142869693/25000000000000000000)
  directionLo := (39362826356416939827/20000000000000000000)
  directionHi := (192201300568442089/97656250000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree017.table
  base := (-2389448381118668219243709498054309281371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-79770924785564165070128606700000000000000)
      constant := (432992656841118048786940689380011216467661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree017.table
  base := (-1219873120761161169654533293323841888431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-1809391189700024096635722085200000000000000)
      constant := (9902349542625023646121073665918844035185445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39362826356416939827/20000000000000000000)
  centralHi := (192201300568442089/97656250000000000)
  directionLo := (1267946021799639097/625000000000000000)
  directionHi := (202871363487942255521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree018.table
  base := (-2985572183897432127503749008928984708219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-27921258251054887414288608000000000000000)
      constant := (158441721104968360526296792023213045875343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree018.table
  base := (-3029445874878122261923385416765908592551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-422241316595195165933818163400000000000000)
      constant := (2416704509998445275702975606165534113335205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1267946021799639097/625000000000000000)
  centralHi := (202871363487942255521/100000000000000000000)
  directionLo := (208752910824682341189/100000000000000000000)
  directionHi := (20875291082468234119/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree019.table
  base := (-3523781795342756536429162806782186797139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-87756624720765159415603041300000000000000)
      constant := (520508059991793359882281737601460318825749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree019.table
  base := (-1780970441710510356637848043940283813449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-1990780659656732396768641385400000000000000)
      constant := (11912984105595071604842067457939185055553155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208752910824682341189/100000000000000000000)
  centralHi := (20875291082468234119/10000000000000000000)
  directionLo := (214473227774700974289/100000000000000000000)
  directionHi := (21447322777470097429/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree020.table
  base := (-1003022563749845904458220558238939561733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-91749474688365656588340258600000000000000)
      constant := (568469229515880204150798391903398175777612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree020.table
  base := (-4045190641158420592653376997054982861557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-4162950789270173093670202071000000000000000)
      constant := (26028358402389456303102822462192731941069415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214473227774700974289/100000000000000000000)
  centralHi := (21447322777470097429/10000000000000000000)
  directionLo := (44008977759734321321/20000000000000000000)
  directionHi := (110022444399335803303/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree021.table
  base := (-4457092605926460079609212910077465565503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-31914108218655384587025825300000000000000)
      constant := (206383105499877764671130529457267603303491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree021.table
  base := (-224286742213618497388132807207514025169/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-241352236623715632989062298400000000000000)
      constant := (1575270143701678739014545597471618688673950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44008977759734321321/20000000000000000000)
  centralHi := (110022444399335803303/50000000000000000000)
  directionLo := (225478914182104266981/100000000000000000000)
  directionHi := (112739457091052133491/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree022.table
  base := (-972844492860491978466343288120218113317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-99735174623566650933814693200000000000000)
      constant := (672499418397446363734899272584590184900735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree022.table
  base := (-4888951637085053159349913723917835369293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-4525729729183589693936040671400000000000000)
      constant := (30803302615461941532958845813893276675436335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225478914182104266981/100000000000000000000)
  centralHi := (112739457091052133491/50000000000000000000)
  directionLo := (23078502636666384989/10000000000000000000)
  directionHi := (230785026366663849891/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree023.table
  base := (-1047591836390950888716665152966980304739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-103728024591167148106551910500000000000000)
      constant := (728479221042873070827075048078985886286745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree023.table
  base := (-52592661822755552382985780197759481629/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-2353559599570148997034479985800000000000000)
      constant := (16685943148999799782893054592810370497012750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23078502636666384989/10000000000000000000)
  centralHi := (230785026366663849891/100000000000000000000)
  directionLo := (5899296358962159949/2500000000000000000)
  directionHi := (235971854358486397961/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree024.table
  base := (-2790998330788114100704419496042421474833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-35906958186255881759763042600000000000000)
      constant := (262351826437225818359171910623745471151002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree024.table
  base := (-2800160283498001736989179573639659259687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-271583814949833683011215515100000000000000)
      constant := (2003285477163698880474937681826215333314085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5899296358962159949/2500000000000000000)
  centralHi := (235971854358486397961/100000000000000000000)
  directionLo := (241047098517496583667/100000000000000000000)
  directionHi := (60261774629374145917/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree025.table
  base := (-2949690828022300874948403960137170858967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-111713724526368142452026345100000000000000)
      constant := (848200772427960031229424357780030924538594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree025.table
  base := (-5915112857011370152506318346063232968207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-5069898139053714594334798572000000000000000)
      constant := (38863845271668068605369743273594390647876165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241047098517496583667/100000000000000000000)
  centralHi := (60261774629374145917/25000000000000000000)
  directionLo := (246017664727605873919/100000000000000000000)
  directionHi := (192201300568442089/78125000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree026.table
  base := (-1548156853203768300225107287782509854563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-115706574493968639624763562400000000000000)
      constant := (911892481164624016276122156389829645235732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree026.table
  base := (-3103055600243299589368968681090756064607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-2625643804505211447233858936100000000000000)
      constant := (20892503373078631777391117040318243793834165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246017664727605873919/100000000000000000000)
  centralHi := (192201300568442089/78125000000000000)
  directionLo := (250889774626917944091/100000000000000000000)
  directionHi := (62722443656729486023/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree027.table
  base := (-3231903610035307861892125615843514709693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-39899808153856378932500259900000000000000)
      constant := (326037315309340883897776063592438911741842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree027.table
  base := (-1618836899192485032181232377956413751873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-301815393275951733033368731800000000000000)
      constant := (2490100002926562423249189266718922762331430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250889774626917944091/100000000000000000000)
  centralHi := (62722443656729486023/25000000000000000000)
  directionLo := (127834528460297715711/50000000000000000000)
  directionHi := (255669056920595431423/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree028.table
  base := (-3357315742205933550477882731093144982877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-123692274429169633970237997000000000000000)
      constant := (1046843773058750197439375039240323390308214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree028.table
  base := (-1344899003625138727389863677246273419327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-5614066548923839494733556472600000000000000)
      constant := (47973547637463607039514041880056296325862825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127834528460297715711/50000000000000000000)
  centralHi := (255669056920595431423/100000000000000000000)
  directionLo := (13018031179962242501/5000000000000000000)
  directionHi := (260360623599244850021/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree029.table
  base := (-1736627818611111302080721911292620712513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-127685124396770131142975214300000000000000)
      constant := (1118075262939356092631091459555965654349532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree029.table
  base := (-6954930869302392260299241451489347319369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-5795456018880547794866475772800000000000000)
      constant := (51239691651590558132328443644216814335655555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13018031179962242501/5000000000000000000)
  centralHi := (260360623599244850021/100000000000000000000)
  directionLo := (66242283501225938063/25000000000000000000)
  directionHi := (264969134004903752253/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree030.table
  base := (-286424428923820906510245762000269998119/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-43892658121456876105237477200000000000000)
      constant := (397265312791165261238880905099979750141075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree030.table
  base := (-3583894609389637496916296529165727400589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-332046971602069783055521948500000000000000)
      constant := (3034431822073604727996120271187542266973495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66242283501225938063/25000000000000000000)
  centralHi := (264969134004903752253/100000000000000000000)
  directionLo := (269498849032105570567/100000000000000000000)
  directionHi := (33687356129013196321/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree031.table
  base := (-7357890249709336068659949337003016827653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-135670824331971125488449648900000000000000)
      constant := (1267997155587071141256389074529472848551123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree031.table
  base := (-920500474330076746897317678005469883447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-3079117479396982197566157186600000000000000)
      constant := (29056706457396228869289696231766138788815860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269498849032105570567/100000000000000000000)
  centralHi := (33687356129013196321/12500000000000000000)
  directionLo := (68488419314851423867/25000000000000000000)
  directionHi := (273953677259405695469/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree032.table
  base := (-1507828442744191669412851648708607620457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-139663674299571622661186866200000000000000)
      constant := (1346671783345166508961060944608112657079435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree032.table
  base := (-7544343380917363490417611542077305723329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-6339624428750672695265233673400000000000000)
      constant := (61720300646460739550413513768338691182051755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68488419314851423867/25000000000000000000)
  centralHi := (273953677259405695469/100000000000000000000)
  directionLo := (69584303608227447063/25000000000000000000)
  directionHi := (278337214432909788253/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree033.table
  base := (-3852510163410480971806765151166983466769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-47885508089057373277974694500000000000000)
      constant := (475937979414188911606619396580498099199386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree033.table
  base := (-3854720479464052993509521480004239500573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-362278549928187833077675165200000000000000)
      constant := (3635565535271983591567082598834809222474215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/25000000000000000000)
  centralHi := (278337214432909788253/100000000000000000000)
  directionLo := (70663194359136051139/25000000000000000000)
  directionHi := (282652777436544204557/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree034.table
  base := (-7856063917002833713346052846974562365661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-147649374234772617006661300800000000000000)
      constant := (1511418766327330437137436223927228938709051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree034.table
  base := (-7859817699557331423063355501025892863713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-6702403368664089295531072273800000000000000)
      constant := (69272838805889134598938700967204513390196235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70663194359136051139/25000000000000000000)
  centralHi := (282652777436544204557/100000000000000000000)
  directionLo := (28690343366176986249/10000000000000000000)
  directionHi := (286903433661769862491/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree035.table
  base := (-7992717945933546370816242140228953159247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-151642224202373114179398518100000000000000)
      constant := (1597482262944454861482805300800439421566777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree035.table
  base := (-7995902716541594894221031007901461648019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-6883792838620797595663991574000000000000000)
      constant := (73218104368377724588860611186549908032552305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28690343366176986249/10000000000000000000)
  centralHi := (286903433661769862491/100000000000000000000)
  directionLo := (291092026516073723769/100000000000000000000)
  directionHi := (29109202651607372377/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree036.table
  base := (-2028837380763682924307987287982165579643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-51878358056657870450711911800000000000000)
      constant := (562000374702988440608364920544214013044284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree036.table
  base := (-8118049329834021331814162033779870316261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-785020256508611766199656763800000000000000)
      constant := (8586203691975606557865307772559905835768255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291092026516073723769/100000000000000000000)
  centralHi := (29109202651607372377/10000000000000000000)
  directionLo := (295221197673127048703/100000000000000000000)
  directionHi := (576603901705326267/195312500000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree037.table
  base := (-8224261529596487740683513691616691902067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-159627924137574108524872952700000000000000)
      constant := (1776972623889790935731491548137949772881397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree037.table
  base := (-822654845568196641832493212501836786121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-3623285889267107097964915087200000000000000)
      constant := (40722953781508579421657446465198780508104975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295221197673127048703/100000000000000000000)
  centralHi := (576603901705326267/195312500000000000)
  directionLo := (299293406559310195589/100000000000000000000)
  directionHi := (29929340655931019559/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree038.table
  base := (-8319703858320109256615620335397812745379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-163620774105174605697610170000000000000000)
      constant := (1870394513252080050402993499131419685291589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree038.table
  base := (-2080409907767296772949756058296243650131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-3713980624245461248031374737300000000000000)
      constant := (42864115180804701248266739261620042643393890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299293406559310195589/100000000000000000000)
  centralHi := (29929340655931019559/10000000000000000000)
  directionLo := (151655473742458048859/50000000000000000000)
  directionHi := (303310947484916097719/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree039.table
  base := (-8401882686261607291009060989502043554499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-55871208024258367623449129100000000000000)
      constant := (655421645534169522141924495818993869336503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree039.table
  base := (-8403520090469174553596906544791605224627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-845483413160847866243963197200000000000000)
      constant := (10013635749288380671543615235114377764891785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151655473742458048859/50000000000000000000)
  centralHi := (303310947484916097719/100000000000000000000)
  directionLo := (153637982379454689419/50000000000000000000)
  directionHi := (307275964758909378839/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree040.table
  base := (-8470968124713475806159711341221007030269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-171606474040375600043084604600000000000000)
      constant := (2064582362939444038139168631929010936727579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree040.table
  base := (-8472352239010618070142672972634460638933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-7790740188404339096328588075000000000000000)
      constant := (94629315934898110332490310674083043441232135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153637982379454689419/50000000000000000000)
  centralHi := (307275964758909378839/100000000000000000000)
  directionLo := (31119046606996093217/10000000000000000000)
  directionHi := (311190466069960932171/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree041.table
  base := (-852710053043540869837132046820876421527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-175599324007976097215821821900000000000000)
      constant := (2165345529052049220476445190848621122062570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree041.table
  base := (-4264134902680627887200772571830425171979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-3986064829180523698230753687600000000000000)
      constant := (49623979387703510709237942219243677805348505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31119046606996093217/10000000000000000000)
  centralHi := (311190466069960932171/100000000000000000000)
  directionLo := (315056334370792319461/100000000000000000000)
  directionHi := (157528167185396159731/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree042.table
  base := (-171407914247680338758743275922888716959/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-59864057991858864796186346400000000000000)
      constant := (756184464219904871568321228461566692456150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree042.table
  base := (-8571382907584132279843527493804853402037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-905946569813083966288269630600000000000000)
      constant := (11553178407478514025932656290298781596908335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315056334370792319461/100000000000000000000)
  centralHi := (157528167185396159731/50000000000000000000)
  directionLo := (159437669232745529277/50000000000000000000)
  directionHi := (63775067693098211711/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree043.table
  base := (-86009492272497966678563774307551114009/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-183585023943177091561296256500000000000000)
      constant := (2374205093752225755537731890585703997391900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree043.table
  base := (-8601782224011438044746543489868700928607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-8334908598274463996727345975600000000000000)
      constant := (108821219885872387641641818192633176123914165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159437669232745529277/50000000000000000000)
  centralHi := (63775067693098211711/20000000000000000000)
  directionLo := (40331142808590405479/12500000000000000000)
  directionHi := (322649142468723243833/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree044.table
  base := (-172376798465272254116159651093087200037/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-187577873910777588734033473800000000000000)
      constant := (2482299922695504859615638615808110759983350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree044.table
  base := (-8619542427252786702960956523371989543341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-8516298068231172296860265275800000000000000)
      constant := (113775771188697412121510222004754344234946895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40331142808590405479/12500000000000000000)
  centralHi := (322649142468723243833/100000000000000000000)
  directionLo := (65275862856073670377/20000000000000000000)
  directionHi := (163189657140184175943/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree045.table
  base := (-2156033215957176050051820022695072250623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-63856907959459361968923563700000000000000)
      constant := (864279097972974258200982050915159132992524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree045.table
  base := (-4312362505760276530726225776665513525551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-483204863232660033166288032000000000000000)
      constant := (6602346370590315993121000868925051891350205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65275862856073670377/20000000000000000000)
  centralHi := (163189657140184175943/50000000000000000000)
  directionLo := (82516833299501852477/25000000000000000000)
  directionHi := (330067333198007409909/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree046.table
  base := (-2154220434877902895078823968407908615267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-195563573845978583079507908400000000000000)
      constant := (2705816724207380636636305268887315289850388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree046.table
  base := (-2154345155113928657274320413733494320861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-4439538504072294448563051938100000000000000)
      constant := (62010294910491309507275158302435869600102590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82516833299501852477/25000000000000000000)
  centralHi := (330067333198007409909/100000000000000000000)
  directionLo := (66742919354420040861/20000000000000000000)
  directionHi := (166857298386050102153/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree047.table
  base := (-1719426171586356831872495735857013653639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-199556423813579080252245125700000000000000)
      constant := (2821237814792303401896641925248934385586245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree047.table
  base := (-8597550963701634645771580461447463713433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-9060466478101297197259023176400000000000000)
      constant := (129310819747362643424477290775943777196059635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66742919354420040861/20000000000000000000)
  centralHi := (166857298386050102153/50000000000000000000)
  directionLo := (168661213496973289559/50000000000000000000)
  directionHi := (337322426993946579119/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree048.table
  base := (-8564916785419876759955634421065583472853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-67849757927059859141660781000000000000000)
      constant := (979700078858905058993498289536803249581441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree048.table
  base := (-4282635197441284650445933446522879609431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-513436441558778083188441248700000000000000)
      constant := (7484050585363774297180291555066470417575605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168661213496973289559/50000000000000000000)
  centralHi := (337322426993946579119/100000000000000000000)
  directionLo := (42611509486765905237/12500000000000000000)
  directionHi := (340892075894127241897/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree049.table
  base := (-4260134850693601803639613493264339044213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-207542123748780074597719560300000000000000)
      constant := (3059403717945914133861203923983741897204166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree049.table
  base := (-2130141802701843237148067451566325255841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-4711622709007356898762430888400000000000000)
      constant := (70113425364165457387714933031866276542768790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/12500000000000000000)
  centralHi := (340892075894127241897/100000000000000000000)
  directionLo := (344424730618648223487/100000000000000000000)
  directionHi := (1345409103979094623/390625000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree050.table
  base := (-4231607257841803679958241281083057943071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-211534973716380571770456777600000000000000)
      constant := (3182148034711251688611520055690504957024722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree050.table
  base := (-8463464721150320249951307079042117092337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-9604634887971422097657781077000000000000000)
      constant := (145852630882293494465294345252987942577603515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344424730618648223487/100000000000000000000)
  centralHi := (1345409103979094623/390625000000000000)
  directionLo := (69584303608227447063/20000000000000000000)
  directionHi := (86980379510284308829/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree051.table
  base := (-8393771790422218229726801789032434508139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-71842607894660356314397998300000000000000)
      constant := (1102444333937903223108236219320402696475583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree051.table
  base := (-8393982129159533766716106736400683149349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1087336039769792266421188930800000000000000)
      constant := (16843360357902242975703455412091969258279295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/20000000000000000000)
  centralHi := (86980379510284308829/25000000000000000000)
  directionLo := (175691754480944815319/50000000000000000000)
  directionHi := (351383508961889630639/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree052.table
  base := (-831195850049060180589058310289098254911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-219520673651581566115931212200000000000000)
      constant := (3434958466479299985698146144873981157058010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree052.table
  base := (-8312135256779345750555661825835228992467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-9967413827884838697923619677400000000000000)
      constant := (157439681336923537161614184247016732258050865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175691754480944815319/50000000000000000000)
  centralHi := (351383508961889630639/100000000000000000000)
  directionLo := (354811721938116579503/100000000000000000000)
  directionHi := (22175732621132286219/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree053.table
  base := (-8217788660979160613579465173279401849843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-223513523619182063288668429500000000000000)
      constant := (3565024302572209015005287768402985383351413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree053.table
  base := (-8217937141674452082015633153918821304783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-10148803297841546998056538977600000000000000)
      constant := (163400939949449343774522609240892877371562885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354811721938116579503/100000000000000000000)
  centralHi := (22175732621132286219/6250000000000000000)
  directionLo := (89551781696057123199/25000000000000000000)
  directionHi := (358207126784228492797/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree054.table
  base := (-8111273844817054572920388254952376340971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-75835457862260853487135215600000000000000)
      constant := (1232510135312024772654997022085142870977087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree054.table
  base := (-1013924816098416342407452703966430103539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-573899598211014183232747682100000000000000)
      constant := (9415223039277550168827784184526042581362980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89551781696057123199/25000000000000000000)
  centralHi := (358207126784228492797/100000000000000000000)
  directionLo := (361570647776244875501/100000000000000000000)
  directionHi := (180785323888122437751/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree055.table
  base := (-7992423609829933381677976777392950901487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-231499223554383057634142864100000000000000)
      constant := (3832476690550465047297374418565963441886617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree055.table
  base := (-7992528275061995225037736851822423483939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-10511582237754963598322377578000000000000000)
      constant := (175658902022500889486132908103761918489004705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361570647776244875501/100000000000000000000)
  centralHi := (180785323888122437751/50000000000000000000)
  directionLo := (364903166590335744907/100000000000000000000)
  directionHi := (91225791647583936227/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree056.table
  base := (-78612458510711187394658553891231483783/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-235492073521983554806880081400000000000000)
      constant := (3969863085359901307705915203497891664595300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree056.table
  base := (-786133368267515727101078301892413577129/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-5346485853855835949227648439100000000000000)
      constant := (90977799469291367432449180942427862506313775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364903166590335744907/100000000000000000000)
  centralHi := (91225791647583936227/25000000000000000000)
  directionLo := (14728221000078743177/4000000000000000000)
  directionHi := (184102762500984289713/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree057.table
  base := (-385887354575185223180319074805910495879/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-79828307829861350659872432900000000000000)
      constant := (1369896510552571751611570734799145370247260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree057.table
  base := (-1543564154681096661724783580346091950761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1208262353074264466509801797600000000000000)
      constant := (20929344779602342141162354196492129311078775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14728221000078743177/4000000000000000000)
  centralHi := (184102762500984289713/50000000000000000000)
  directionLo := (92869631842268646513/25000000000000000000)
  directionHi := (371478527369074586053/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree058.table
  base := (-378096636091118569897037068088053119623/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-243477773457184549152354516000000000000000)
      constant := (4251955980927654761089194744894150438467860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree058.table
  base := (-472624657158755855695108099275239710781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-5527875323812544249360567739300000000000000)
      constant := (97442206122132319479878663789388223337069560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92869631842268646513/25000000000000000000)
  centralHi := (371478527369074586053/100000000000000000000)
  directionLo := (187361471459994466461/50000000000000000000)
  directionHi := (374722942919988932923/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree059.table
  base := (-7393807198315577568939745125720933990833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-247470623424785046325091733300000000000000)
      constant := (4396662393063123704231125533731011594082503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree059.table
  base := (-7393859004880173203096772023187745934691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-11237140117581796798854054778800000000000000)
      constant := (201516524962098934095026796968478962896450145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187361471459994466461/50000000000000000000)
  centralHi := (374722942919988932923/100000000000000000000)
  directionLo := (188969753932301472691/50000000000000000000)
  directionHi := (377939507864602945383/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree060.table
  base := (-3606687103055543474966900777952881243823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-83821157797461847832609650200000000000000)
      constant := (1514602911632657402833510297332282712537062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree060.table
  base := (-3606708813947441276626683944746524878931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-634362754863250283277054115500000000000000)
      constant := (11570024433312164143846908069486406380448105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188969753932301472691/50000000000000000000)
  centralHi := (377939507864602945383/100000000000000000000)
  directionLo := (381128927345142957543/100000000000000000000)
  directionHi := (47641115918142869693/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree061.table
  base := (-1404127358772542765785924098686571185503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-255456323359986040670566167900000000000000)
      constant := (4693394978994315945305350431121604296652365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree061.table
  base := (-3510336588913667665442069627776395347779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-5799959528747606699559946689600000000000000)
      constant := (107558077812578119719373230243985559884149505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381128927345142957543/100000000000000000000)
  centralHi := (47641115918142869693/12500000000000000000)
  directionLo := (384291877241219147413/100000000000000000000)
  directionHi := (192145938620609573707/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree062.table
  base := (-3407798742437987803304386478184274337307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-259449173327586537843303385200000000000000)
      constant := (4845421102642405258039450011942683061928474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree062.table
  base := (-6815627963531016885594666530759972212421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-11781308527451921699252812679400000000000000)
      constant := (222083671503625127076942882614322211253969495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384291877241219147413/100000000000000000000)
  centralHi := (192145938620609573707/50000000000000000000)
  directionLo := (193714502921116643589/50000000000000000000)
  directionHi := (387429005842233287179/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree063.table
  base := (-263930334751828218111294533534725661641/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-87814007765062345005346867500000000000000)
      constant := (1666629029011812216058176564972395575376925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree063.table
  base := (-1319656778794159201169595625922315396459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1329188666378736666598414664400000000000000)
      constant := (25462554073543871738278453902437479035796725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193714502921116643589/50000000000000000000)
  centralHi := (387429005842233287179/100000000000000000000)
  directionLo := (390540935398867275031/100000000000000000000)
  directionHi := (48817616924858409379/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree064.table
  base := (-796077647157138277941333973613718894061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-267434873262787532188777819800000000000000)
      constant := (5156792916588693290005866958699812239627608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree064.table
  base := (-3184321274313805181558883666407907702817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6072043733682669149759325639900000000000000)
      constant := (118177050230137807692244611116064797380359115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390540935398867275031/100000000000000000000)
  centralHi := (48817616924858409379/12500000000000000000)
  directionLo := (39362826356416939827/10000000000000000000)
  directionHi := (393628263564169398271/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree065.table
  base := (-3063343673153219808980948866436588067513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-271427723230388029361515037100000000000000)
      constant := (5316138578377758828241488008466641414784766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree065.table
  base := (-3063352617736820174947495663149383248917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6162738468661023299825785290000000000000000)
      constant := (121828506184519351618966728142299499784188615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39362826356416939827/10000000000000000000)
  centralHi := (393628263564169398271/100000000000000000000)
  directionLo := (79338312946738210191/20000000000000000000)
  directionHi := (99172891183422762739/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree066.table
  base := (-5872458067906439131731003199521668208933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-91806857732662842178084084800000000000000)
      constant := (1825974687224989553806832728651434995373201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree066.table
  base := (-5872473038713626734727603388238140119279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1389651823030972766642721097800000000000000)
      constant := (27896857994342354354841874022409283694632445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79338312946738210191/20000000000000000000)
  centralHi := (99172891183422762739/25000000000000000000)
  directionLo := (399731391293184760287/100000000000000000000)
  directionHi := (12491605977912023759/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree067.table
  base := (-2802967166218189538459312108887146708691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-279413423165589023706989471700000000000000)
      constant := (5642149357566909320734171766902531359243562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree067.table
  base := (-140148671452501805300741974616103779283/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6344127938617731599958704590200000000000000)
      constant := (129299114418001654830090875709824559387807700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399731391293184760287/100000000000000000000)
  centralHi := (12491605977912023759/3125000000000000000)
  directionLo := (6292941793461549389/1562500000000000000)
  directionHi := (402748274781539160897/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree068.table
  base := (-5327116963762482790360183602455811521587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-283406273133189520879726689000000000000000)
      constant := (5808814458638784796150989945977897696305717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree068.table
  base := (-1331781860327672032183664773586807570273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6434822673596085750025164240300000000000000)
      constant := (133118266363497795771120034171034685868078870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6292941793461549389/1562500000000000000)
  centralHi := (402748274781539160897/100000000000000000000)
  directionLo := (1267946021799639097/312500000000000000)
  directionHi := (405742726975884511041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree069.table
  base := (-5036006648178601612004244122250413838139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-95799707700263339350821302100000000000000)
      constant := (1992639786237983475203805219420748758485583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree069.table
  base := (-2518007705306748258034106570817060922553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-725057489841604433343513765600000000000000)
      constant := (15221479631668860328728078936228232258485115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1267946021799639097/312500000000000000)
  centralHi := (405742726975884511041/100000000000000000000)
  directionLo := (408715240905141862741/100000000000000000000)
  directionHi := (204357620452570931371/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree070.table
  base := (-591575494786200564864911164731072731463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-291391973068390515225201123600000000000000)
      constant := (6149464052638962388321832551889362763334664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree070.table
  base := (-4732611284828504476360963789770871550069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-13232424287105588100316167081000000000000000)
      constant := (281848530555012889908333906771142797022222055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408715240905141862741/100000000000000000000)
  centralHi := (204357620452570931371/50000000000000000000)
  directionLo := (82333258359540012997/20000000000000000000)
  directionHi := (205833145898850032493/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree071.table
  base := (-35335274981777923099906052446305924139/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-295384823035991012397938340900000000000000)
      constant := (6323448536106179944394794190560405835343625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree071.table
  base := (-88338309948332495741720751571536035667/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6706906878531148200224543190600000000000000)
      constant := (144911112053182066920524454925273197638871625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82333258359540012997/20000000000000000000)
  centralHi := (205833145898850032493/50000000000000000000)
  directionLo := (103649084492094683991/25000000000000000000)
  directionHi := (82919267593675747193/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree072.table
  base := (-4088923292393402807739072323842947013919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-99792557667863836523558519400000000000000)
      constant := (2166624268502450350506683078628471158958243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree072.table
  base := (-408892841137976529698392237749938533079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-755289068167722483365666982300000000000000)
      constant := (16550428548726524724250585139066263830057225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103649084492094683991/25000000000000000000)
  centralHi := (82919267593675747193/20000000000000000000)
  directionLo := (208752910824682341189/50000000000000000000)
  directionHi := (417505821649364682379/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree073.table
  base := (-3748646053937992730168144311980719851581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-303370522971192006743412775500000000000000)
      constant := (6678736857812761601143130018654673521335771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree073.table
  base := (-937162582883796574128331637694401133209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-6888296348487856500357462490800000000000000)
      constant := (153052499871850916538541498920782535082100710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208752910824682341189/50000000000000000000)
  centralHi := (417505821649364682379/100000000000000000000)
  directionLo := (420395169769387453609/100000000000000000000)
  directionHi := (42039516976938745361/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree074.table
  base := (-3396077940793194572176869792308201429337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-307363372938792503916149992800000000000000)
      constant := (6860040690471476933507423963419226187135967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree074.table
  base := (-3396081514627748579882970052601712745179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-13957982166932421300847844281800000000000000)
      constant := (314414081602255629341111774284216306338202505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420395169769387453609/100000000000000000000)
  centralHi := (42039516976938745361/10000000000000000000)
  directionLo := (423264794685021124093/100000000000000000000)
  directionHi := (211632397342510562047/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree075.table
  base := (-606243838469808862542041963080680406983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-103785407635464333696295736700000000000000)
      constant := (2347928100442995574934142140241289793895255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree075.table
  base := (-3031222177661773772139144206420226568719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1571041292987681066775640398000000000000000)
      constant := (35870551040539120396717012649461089804407645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423264794685021124093/100000000000000000000)
  centralHi := (211632397342510562047/50000000000000000000)
  directionLo := (42611509486765905237/10000000000000000000)
  directionHi := (426115094867659052371/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree076.table
  base := (-2654070011503445849582753575641970473009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-315349072873993498261624427400000000000000)
      constant := (7229967688559209839947806087819222265742919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree076.table
  base := (-2654072504766807432140417017848820696177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-14320761106845837901113682882200000000000000)
      constant := (331367632956918729813769296482091227618048315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42611509486765905237/10000000000000000000)
  centralHi := (426115094867659052371/100000000000000000000)
  directionLo := (428946455549401948579/100000000000000000000)
  directionHi := (21447322777470097429/5000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree077.table
  base := (-2264630570900621665907067898707732834081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-319341922841593995434361644700000000000000)
      constant := (7418590850608348276595549863274130404493271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree077.table
  base := (-283079081607007231979897742536300700989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-7251075288401273100623301091200000000000000)
      constant := (170006051157452859355599801423206192864397820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428946455549401948579/100000000000000000000)
  centralHi := (21447322777470097429/5000000000000000000)
  directionLo := (2158796246654116553/500000000000000000)
  directionHi := (431759249330823310601/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree078.table
  base := (-186290101808316886156931393215662829179/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-107778257603064830869032954000000000000000)
      constant := (2536551262049506220282227432253530115124630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree078.table
  base := (-1862902756290574493021790208431797282043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1631504449639917166819946831400000000000000)
      constant := (38752040820488536137286728965340569122308065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2158796246654116553/500000000000000000)
  centralHi := (431759249330823310601/100000000000000000000)
  directionLo := (434553836753326844949/100000000000000000000)
  directionHi := (8691076735066536899/2000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree079.table
  base := (-45277546242113110435571458317311899663/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-327327622776794989779836079300000000000000)
      constant := (7803156494039452203824884233367114172897056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree079.table
  base := (-28977658614491929022087943382953373023/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-7432464758357981400756220391400000000000000)
      constant := (178818214059276041274204313545782597098142125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434553836753326844949/100000000000000000000)
  centralHi := (8691076735066536899/2000000000000000000)
  directionLo := (437330566838584957251/100000000000000000000)
  directionHi := (109332641709646239313/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree080.table
  base := (-255643016315045050712839900109413238901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-331320472744395486952573296600000000000000)
      constant := (7999098973296853046851619311596061123399564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree080.table
  base := (-1022573276276516879482737508670459952113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-15046318986672671101645360083000000000000000)
      constant := (366616284476823541424178529508988463719394235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437330566838584957251/100000000000000000000)
  centralHi := (109332641709646239313/25000000000000000000)
  directionLo := (44008977759734321321/10000000000000000000)
  directionHi := (440089777597343213211/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree081.table
  base := (-291986434780957502081460497778342708281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-111771107570665328041770171300000000000000)
      constant := (2732493741022083870901399345700829943750314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree081.table
  base := (-583973880144398388491895152578214547983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1691967606292153266864253264800000000000000)
      constant := (41745326269321776278411617661163980345340765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44008977759734321321/10000000000000000000)
  centralHi := (440089777597343213211/100000000000000000000)
  directionLo := (221415898254845286527/50000000000000000000)
  directionHi := (88566359301938114611/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree082.table
  base := (-133083975570024135285958817972658983009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-339306172679596481298047731200000000000000)
      constant := (8398303242601393099605903518188246069152919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree082.table
  base := (-4158900586374090401656911622055104329/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-7704548963293043850955599341700000000000000)
      constant := (192455691964406473588762324616129082923948080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221415898254845286527/50000000000000000000)
  centralHi := (88566359301938114611/20000000000000000000)
  directionLo := (222778470489363596657/50000000000000000000)
  directionHi := (89111388195745438663/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree083.table
  base := (33009454383678696874510378979891057213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-343299022647196978470784948500000000000000)
      constant := (8601565031246369158641425946570690195149170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree083.table
  base := (165046920205124951080425837959187271027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-7795243698271398001022058991800000000000000)
      constant := (197113313482127672289501611043788470844765935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222778470489363596657/50000000000000000000)
  centralHi := (89111388195745438663/20000000000000000000)
  directionLo := (224132759379704451599/50000000000000000000)
  directionHi := (448265518759408903199/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree084.table
  base := (80556262417624358771873404136192184617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-115763957538265825214507388600000000000000)
      constant := (2935755529473613105776287175724085765538510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree084.table
  base := (80556203743432332470978556321265449379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-876215381472194683454279849100000000000000)
      constant := (22425203639219215707669172372012284726110275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224132759379704451599/50000000000000000000)
  centralHi := (448265518759408903199/100000000000000000000)
  directionLo := (450957828364208533963/100000000000000000000)
  directionHi := (112739457091052133491/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree085.table
  base := (323330052000959170963764799026215810607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-351284722582397972816259383100000000000000)
      constant := (9015407913607802994328191405327443769181852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree085.table
  base := (1293319718660046752805995696110158300999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-15953266336456212602309956584000000000000000)
      constant := (413192499532157039592745238216674614111904595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450957828364208533963/100000000000000000000)
  centralHi := (112739457091052133491/25000000000000000000)
  directionLo := (453634159447107720361/100000000000000000000)
  directionHi := (226817079723553860181/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree086.table
  base := (179336724378812684907191675553058739373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-355277572549998469988996600400000000000000)
      constant := (9225989006343477234966676118549775286543570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree086.table
  base := (1793366835730895784708205336870303806889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-16134655806412920902442875884200000000000000)
      constant := (422843129023304422760398411570152473041790045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453634159447107720361/100000000000000000000)
  centralHi := (226817079723553860181/50000000000000000000)
  directionLo := (456294793167317369807/100000000000000000000)
  directionHi := (28518424572957335613/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree087.table
  base := (1152851842489615094218224007114239145363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-119756807505866322387244605900000000000000)
      constant := (3146336622069637694729973312830185434872178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree087.table
  base := (2305703344751663628008673406602965160469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1812893919596625466952866131600000000000000)
      constant := (48067283773512274832231054179967133432221105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456294793167317369807/100000000000000000000)
  centralHi := (28518424572957335613/6250000000000000000)
  directionLo := (229470001267009804933/50000000000000000000)
  directionHi := (458940002534019609867/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree088.table
  base := (88447796538650931521496015504618867821/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-363263272485199464334471035000000000000000)
      constant := (9654470492823047689958575840865330233932448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree088.table
  base := (1415164602800632564359237499142367927209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-8248717373163168751354357242300000000000000)
      constant := (221239887165413076147211475888992659010519645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229470001267009804933/50000000000000000000)
  centralHi := (458940002534019609867/100000000000000000000)
  directionLo := (461570052733327699781/100000000000000000000)
  directionHi := (230785026366663849891/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree089.table
  base := (3367244617789939672920189165470730017863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-367256122452799961507208252300000000000000)
      constant := (9872370885836942177940489816351736570160767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree089.table
  base := (3367244381363558478274531525029669741239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-16678824216283045802841633784800000000000000)
      constant := (452465790116000421740960757217307016245201795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461570052733327699781/100000000000000000000)
  centralHi := (230785026366663849891/50000000000000000000)
  directionLo := (58023150179821531789/12500000000000000000)
  directionHi := (464185201438572254313/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree090.table
  base := (3916449034905501394190600287365731263843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-123749657473466819559981823200000000000000)
      constant := (3364237014976333007551058895112097193791529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree090.table
  base := (3916448837855473700552221193623475569151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1873357076248861566997172565000000000000000)
      constant := (51395955700365459832151381345713056400611795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58023150179821531789/12500000000000000000)
  centralHi := (464185201438572254313/100000000000000000000)
  directionLo := (93357139820988279651/20000000000000000000)
  directionHi := (29174106194058837391/6250000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree091.table
  base := (4477942707446899198519565786412155806843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-375241822388000955852682686900000000000000)
      constant := (10315490969800988682130820587140209402261587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree091.table
  base := (895588508647077928660406773149527437161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-17041603156196462403107472385200000000000000)
      constant := (472773207879796445972966924854297793060251025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93357139820988279651/20000000000000000000)
  centralHi := (29174106194058837391/6250000000000000000)
  directionLo := (58671473656178556233/12500000000000000000)
  directionHi := (93874357849885689973/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree092.table
  base := (1262931401126695598237083914926823761473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-379234672355601453025419904200000000000000)
      constant := (10540710660174745000136792771737365655413028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree092.table
  base := (315732841729856799187623304783147212229/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-8611496313076585351620195842700000000000000)
      constant := (241547304916721488598183913398337396967621960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58671473656178556233/12500000000000000000)
  centralHi := (93874357849885689973/20000000000000000000)
  directionLo := (5899296358962159949/1250000000000000000)
  directionHi := (471943708716972795921/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree093.table
  base := (2818898848550655410461376708423599641383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-127742507441067316732719040500000000000000)
      constant := (3589456705263137805087368610238041597848298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree093.table
  base := (2818898791551027846251336993168217467893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-966910116450548833520739499200000000000000)
      constant := (27418211508492010005928313634527569786055185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5899296358962159949/1250000000000000000)
  centralHi := (471943708716972795921/100000000000000000000)
  directionLo := (474501687933617209647/100000000000000000000)
  directionHi := (29656355495851075603/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree094.table
  base := (3118079478957594056713734361195146769029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-387220372290802447370894338800000000000000)
      constant := (10998469336399156260185621611051512641842522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree094.table
  base := (779519857868445519615096422695290450271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-8792885783033293651753115142900000000000000)
      constant := (252036399913639451945912308787126370529439020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474501687933617209647/100000000000000000000)
  centralHi := (29656355495851075603/6250000000000000000)
  directionLo := (477045951147447471453/100000000000000000000)
  directionHi := (238522975573723735727/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree095.table
  base := (1369361872217740697514954137550885788581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-391213222258402944543631556100000000000000)
      constant := (11231008321771236137861350714752289860486145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree095.table
  base := (427925580124024836161181470257903817147/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-8883580518011647801819574793000000000000000)
      constant := (257364793923246532323516705916010608367556280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477045951147447471453/100000000000000000000)
  centralHi := (238522975573723735727/50000000000000000000)
  directionLo := (479576716658027328757/100000000000000000000)
  directionHi := (239788358329013664379/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree096.table
  base := (3734874441019767119852617357970260101743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-131735357408667813905456257800000000000000)
      constant := (3821995690561470714652119440147821560610458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree096.table
  base := (7469748816156028242500887843315762584739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-1994283389553333767085785431800000000000000)
      constant := (58388685688972863210085630472629209316313255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479576716658027328757/100000000000000000000)
  centralHi := (239788358329013664379/50000000000000000000)
  directionLo := (241047098517496583667/50000000000000000000)
  directionHi := (96418839406998633467/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree097.table
  base := (405248874865666235777681354069264071683/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-399198922193603938889105990700000000000000)
      constant := (11703405585927595077582257324594967532902940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree097.table
  base := (1013122180305868198503821427987765064403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-9064969987968356101952494093200000000000000)
      constant := (268189274940372867301485331454255179404332860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241047098517496583667/50000000000000000000)
  centralHi := (96418839406998633467/20000000000000000000)
  directionLo := (96919719865285579037/20000000000000000000)
  directionHi := (242299299663213947593/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree098.table
  base := (1750499036891620053057657334677424707151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-403191772161204436061843208000000000000000)
      constant := (11943263864298717166890562777210484111821795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree098.table
  base := (4376247569385695059344417938932805143199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-9155664722946710252018953743300000000000000)
      constant := (273685361938759114634279667424707786082995595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96919719865285579037/20000000000000000000)
  centralHi := (242299299663213947593/50000000000000000000)
  directionLo := (487090125257592129441/100000000000000000000)
  directionHi := (243545062628796064721/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree099.table
  base := (9412301921918435156851048442965703264703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-135728207376268311078193475100000000000000)
      constant := (4061853968867926526764250397616397109794109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree099.table
  base := (9412301883879495954242989270359621561073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2054746546205569867130091865200000000000000)
      constant := (62052743686940784134004716649196182970248285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487090125257592129441/100000000000000000000)
  centralHi := (243545062628796064721/50000000000000000000)
  directionLo := (122392242855138131957/25000000000000000000)
  directionHi := (489568971420552527829/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree100.table
  base := (10084397688946003513575439978603997829457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-411177472096405430407317642600000000000000)
      constant := (12430299712656047384898824319807435980465113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree100.table
  base := (10084397657277849928354166061949520461479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-18674108385806837104303746087000000000000000)
      constant := (569690457787292386083052767345089555786898995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122392242855138131957/25000000000000000000)
  centralHi := (489568971420552527829/100000000000000000000)
  directionLo := (246017664727605873919/50000000000000000000)
  directionHi := (492035329455211747839/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree101.table
  base := (10768782465523728367883622142847233924551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-415170322064005927580054859900000000000000)
      constant := (12677477282275366888000581605848125105320959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree101.table
  base := (10768782439162004661615413163221066824617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-18855497855763545404436665387200000000000000)
      constant := (581018017683973414710930471355174532063969885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246017664727605873919/50000000000000000000)
  centralHi := (492035329455211747839/100000000000000000000)
  directionLo := (494489386222211803993/100000000000000000000)
  directionHi := (247244693111105901997/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree102.table
  base := (2293091246460245516951848435195761566499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-139721057343868808250930692400000000000000)
      constant := (4309031538429194883460958625377936423497485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree102.table
  base := (11465456210358912998355361349115871670613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2115209702857805967174398298600000000000000)
      constant := (65828596984971673221292073037430214225177585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494489386222211803993/100000000000000000000)
  centralHi := (247244693111105901997/50000000000000000000)
  directionLo := (24846566198407615211/5000000000000000000)
  directionHi := (496931323968152304221/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree103.table
  base := (2434883794107930922313299817979483045221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-423156021999206921925529294500000000000000)
      constant := (13179151711524051053071984921771576737034945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree103.table
  base := (12174418952277606895793449809696071095417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-19218276795676962004702503987600000000000000)
      constant := (604008523322077976867821198162156908793643885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24846566198407615211/5000000000000000000)
  centralHi := (496931323968152304221/100000000000000000000)
  directionLo := (124840330120884244739/25000000000000000000)
  directionHi := (499361320483536978957/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree104.table
  base := (12895670662064361526378094870527304741391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-427148871966807419098266511800000000000000)
      constant := (13433648570821194264770563060634745742672519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree104.table
  base := (6447835323433368362180177345987699817593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-9699833132816835152417711643900000000000000)
      constant := (307835734524330685869766258835285018426125165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124840330120884244739/25000000000000000000)
  centralHi := (499361320483536978957/100000000000000000000)
  directionLo := (250889774626917944091/50000000000000000000)
  directionHi := (501779549253835888183/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree105.table
  base := (3407302822306020968046897837738774488699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-143713907311469305423667909700000000000000)
      constant := (4563528397673384301788517449740365293864388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree105.table
  base := (1703651409572228529308399168360683504721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1087836429755021033609352366000000000000000)
      constant := (34858122779854895085315506577179923030849780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250889774626917944091/50000000000000000000)
  centralHi := (501779549253835888183/100000000000000000000)
  directionLo := (252093089802013267969/50000000000000000000)
  directionHi := (504186179604026535939/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree106.table
  base := (7187520417427785666840182926805510319521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-435134571902008413443740946400000000000000)
      constant := (13949961577966457722019121183432499185751378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree106.table
  base := (7187520412166656635470896579925480464229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-9881222602773543452550630944100000000000000)
      constant := (319666373140670890576708135204629819588012745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252093089802013267969/50000000000000000000)
  centralHi := (504186179604026535939/100000000000000000000)
  directionLo := (126645344209238671917/25000000000000000000)
  directionHi := (506581376836954687669/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree107.table
  base := (1513315928225277373182490985476509271197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-439127421869608910616478163700000000000000)
      constant := (14211777725509754263119985986555385834407730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree107.table
  base := (3026631854699710833399815241762977960347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-19943834675503795205234181188400000000000000)
      constant := (651331077773785352337696017172200030369702675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126645344209238671917/25000000000000000000)
  centralHi := (506581376836954687669/100000000000000000000)
  directionLo := (508965302365834835317/100000000000000000000)
  directionHi := (254482651182917417659/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree108.table
  base := (15903566615139844923279552987409808112269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-147706757279069802596405127000000000000000)
      constant := (4825344545167853304459357241762229424336807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree108.table
  base := (3180713321571443359274695872647682116623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2236136016162278167263011165400000000000000)
      constant := (73715689389794578863042311734465728476240175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508965302365834835317/100000000000000000000)
  centralHi := (254482651182917417659/50000000000000000000)
  directionLo := (127834528460297715711/25000000000000000000)
  directionHi := (102267622768238172569/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree109.table
  base := (3337252563529470728592945621175703613307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-447113121804809904961952598300000000000000)
      constant := (14742729307805049791407662295315406662598815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree109.table
  base := (3337252562317891717304499517209534598807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-20306613615417211805500019788800000000000000)
      constant := (675663126478032317200590921183219307562584175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127834528460297715711/25000000000000000000)
  centralHi := (102267622768238172569/20000000000000000000)
  directionLo := (128424991318129854079/25000000000000000000)
  directionHi := (513699965272519416317/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree110.table
  base := (17481247874291194777803789784231051236303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-451105971772410402134689815600000000000000)
      constant := (15011864742274866951191067887808079461126727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree110.table
  base := (3496249573850497916327159397318992662783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-20488003085373920105632939089000000000000000)
      constant := (687996843677174344705223178665570960142135575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128424991318129854079/25000000000000000000)
  centralHi := (513699965272519416317/100000000000000000000)
  directionLo := (516051007144941673327/100000000000000000000)
  directionHi := (32253187946558854583/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree111.table
  base := (4572130442488445212820697161253096712517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-151699607246670299769142344300000000000000)
      constant := (5094479979592317701813220986122537160550204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree111.table
  base := (29261634825221024538700158289339738787/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2296599172814514267307317598800000000000000)
      constant := (77826928455496512072893570856717680153384375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516051007144941673327/100000000000000000000)
  centralHi := (32253187946558854583/6250000000000000000)
  directionLo := (64798923316386692591/12500000000000000000)
  directionHi := (518391386531093540729/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree112.table
  base := (19108084489867164803510054047568038771483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-459091671707611396480164250200000000000000)
      constant := (15557454897178396730614422471228112348943347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree112.table
  base := (19108084486382132859782758776497143882667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-20850782025287336705898777689400000000000000)
      constant := (712999663738945701466330264737761343272480135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64798923316386692591/12500000000000000000)
  centralHi := (518391386531093540729/100000000000000000000)
  directionLo := (520721247198489700041/100000000000000000000)
  directionHi := (260360623599244850021/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree113.table
  base := (4984984004899451021635590298924588569439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-463084521675211893652901467500000000000000)
      constant := (15833909617349295943783857403223785188499804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree113.table
  base := (19939936016699802335503985437236565314809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-21032171495244045006031696989600000000000000)
      constant := (725668766589769708885843556857510808952497645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520721247198489700041/100000000000000000000)
  centralHi := (260360623599244850021/50000000000000000000)
  directionLo := (104608145942516657327/20000000000000000000)
  directionHi := (130760182428145821659/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree114.table
  base := (324751192891136325296419624774128413227/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-155692457214270796941879561600000000000000)
      constant := (5370934699720877993338429355806632655339584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree114.table
  base := (1299004771413941242528293661867996353483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1178531164733375183675812016100000000000000)
      constant := (41024981369235162773155866057712478687253880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104608145942516657327/20000000000000000000)
  centralHi := (130760182428145821659/25000000000000000000)
  directionLo := (262674985767865129141/50000000000000000000)
  directionHi := (525349971535730258283/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree115.table
  base := (4328101090473377007724129142656849640691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-471070221610412887998375902100000000000000)
      constant := (16394138342494165461649140429482058233831095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree115.table
  base := (1082025272518171084384468317002299438903/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-10697475217578730803148767795000000000000000)
      constant := (375671178951375514308702925432234312727557150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262674985767865129141/50000000000000000000)
  centralHi := (525349971535730258283/100000000000000000000)
  directionLo := (527649107122255614119/100000000000000000000)
  directionHi := (13191227678056390353/2500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree116.table
  base := (11254611664045784713885251700166824990173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-475063071578013385171113119400000000000000)
      constant := (16677912347222311950825923446603002849823114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree116.table
  base := (22509223326425958913807236311112111703521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-21576339905114169906430454890200000000000000)
      constant := (764346846353858558806064607621920405239926005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527649107122255614119/100000000000000000000)
  centralHi := (13191227678056390353/2500000000000000000)
  directionLo := (66242283501225938063/12500000000000000000)
  directionHi := (105987653601961500901/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree117.table
  base := (1461889372436479717160492529432485003637/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-159685307181871294114616778900000000000000)
      constant := (5654708704409355174979654727200259280174576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree117.table
  base := (11695114978799523312585916699895839423109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1208762743059493233697965232800000000000000)
      constant := (43192396110789156243592216494130312774039905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66242283501225938063/12500000000000000000)
  centralHi := (105987653601961500901/20000000000000000000)
  directionLo := (106443516581434973851/20000000000000000000)
  directionHi := (66527197863396858657/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree118.table
  base := (12141762666047886939164639688926432597757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-483048771513214379516587554000000000000000)
      constant := (17252779640394899320282111156550675786759626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree118.table
  base := (12141762665472404966592172146315237269399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-10969559422513793253348146745300000000000000)
      constant := (395345604409274975011654599644897671094106595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106443516581434973851/20000000000000000000)
  centralHi := (66527197863396858657/12500000000000000000)
  directionLo := (133621794444683626059/25000000000000000000)
  directionHi := (534487177778734504237/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree119.table
  base := (12594554717373422465629091717079339716679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-487041621480814876689324771300000000000000)
      constant := (17543872928608684159485195721269928114900222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree119.table
  base := (12594554716895090920481606870873760665343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11060254157492147403414606395400000000000000)
      constant := (402015541410880689794137742466438873069463915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133621794444683626059/25000000000000000000)
  centralHi := (534487177778734504237/100000000000000000000)
  directionLo := (268373587962842168199/50000000000000000000)
  directionHi := (536747175925684336399/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree120.table
  base := (26106982254513608296542259837126691898091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-163678157149471791287353996200000000000000)
      constant := (5945801992585870173172302293511380075694273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree120.table
  base := (26106982253718500895779081950772941812387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2477988642771222567440236899000000000000000)
      constant := (90831416888756705910133707011784782381557415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268373587962842168199/50000000000000000000)
  centralHi := (536747175925684336399/100000000000000000000)
  directionLo := (269498849032105570567/50000000000000000000)
  directionHi := (107799539612842228227/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree121.table
  base := (5407428755844475323095251044226067345301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-495027321416015871034799205900000000000000)
      constant := (18133378787732115214148897354052673030538545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree121.table
  base := (6759285944640396996825285458840212785781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11241643627448855703547525695600000000000000)
      constant := (415523108172384379146204428470095572356482610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269498849032105570567/50000000000000000000)
  centralHi := (107799539612842228227/20000000000000000000)
  directionLo := (270619431200366461311/50000000000000000000)
  directionHi := (541238862400732922623/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree122.table
  base := (27979593996941374178613949325973011065893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-499020171383616368207536423200000000000000)
      constant := (18431791358424812261996151159483757099593037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree122.table
  base := (27979593996392250958473692674402093741659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-22664676724854419707227970691400000000000000)
      constant := (844721475854806082068284407643212847965371895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270619431200366461311/50000000000000000000)
  centralHi := (541238862400732922623/100000000000000000000)
  directionLo := (543470784704348660379/100000000000000000000)
  directionHi := (27173539235217433019/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree123.table
  base := (14467166447986735435665644074122434314397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-167671007117072288460091213500000000000000)
      constant := (6244214563243475830675683936932234605886382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree123.table
  base := (14467166447758586719577355434094698160927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1269225899711729333742271666200000000000000)
      constant := (47694918362454807299384583092069261417241715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543470784704348660379/100000000000000000000)
  centralHi := (27173539235217433019/5000000000000000000)
  directionLo := (545693578376621068957/100000000000000000000)
  directionHi := (272846789188310534479/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree124.table
  base := (1868835029053080566813779190540488262631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-507005871318817362553010857800000000000000)
      constant := (19035935781545736505620129066237830309818864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree124.table
  base := (14950680232235075374464839081301293804321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11513727832383918153746904645900000000000000)
      constant := (436203690174133146679377620544687023990750005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545693578376621068957/100000000000000000000)
  centralHi := (272846789188310534479/50000000000000000000)
  directionLo := (68488419314851423867/12500000000000000000)
  directionHi := (547907354518811390937/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree125.table
  base := (15440338346160323686351332655617422869009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-510998721286417859725748075100000000000000)
      constant := (19341667633769505670184573539363613611642162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree125.table
  base := (7720169173001410268139738770386995024407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11604422567362272303813364296000000000000000)
      constant := (443209012661245461771305294975888465969769670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68488419314851423867/12500000000000000000)
  centralHi := (547907354518811390937/100000000000000000000)
  directionLo := (550112221996679016513/100000000000000000000)
  directionHi := (275056110998339508257/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree126.table
  base := (15936140783677155128911253733426405314201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-171663857084672785632828430800000000000000)
      constant := (6549946415434145288666462283650558431885206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree126.table
  base := (31872281567092604577007293455765179236263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2598914956075694767528849765800000000000000)
      constant := (100060051715821427867567696303989433065631835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550112221996679016513/100000000000000000000)
  centralHi := (275056110998339508257/50000000000000000000)
  directionLo := (276154143751476434569/50000000000000000000)
  directionHi := (552308287502952869139/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree127.table
  base := (8219043769781504258878629702407474590563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-518984421221618854071222509700000000000000)
      constant := (19960450619047108746864779728649169085260268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree127.table
  base := (8219043769727151716919180722050480692611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11785812037318980603946283596200000000000000)
      constant := (457387350351794494612719546715475889361014910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276154143751476434569/50000000000000000000)
  centralHi := (552308287502952869139/100000000000000000000)
  directionLo := (554495655617575990489/100000000000000000000)
  directionHi := (55449565561757599049/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree128.table
  base := (271138857736118137150269082078098099431/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-522977271189219351243959727000000000000000)
      constant := (20273501751907935307722796595737860361859875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree128.table
  base := (529568081513033848450386496348537858617/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-11876506772297334754012743246300000000000000)
      constant := (464560365550889224364442177226917050647676320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554495655617575990489/100000000000000000000)
  centralHi := (55449565561757599049/10000000000000000000)
  directionLo := (69584303608227447063/12500000000000000000)
  directionHi := (111334885773163915301/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree129.table
  base := (3492082797059734181733290556971519400937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-175656707052273282805565648100000000000000)
      constant := (6862997548263702193228588296996645582028110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree129.table
  base := (34920827970447327284359475784298771024881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2659378112727930867573156199200000000000000)
      constant := (104842061848082259700405316444523444696119645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69584303608227447063/12500000000000000000)
  centralHi := (111334885773163915301/20000000000000000000)
  directionLo := (279422353887178918833/50000000000000000000)
  directionHi := (558844707774357837667/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree130.table
  base := (35961587329643044729571840550464943860449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-530962971124420345589434161600000000000000)
      constant := (20906923297604546295814370211704184494744041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree130.table
  base := (35961587329518443896967136268433418939363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-24115792484508086108291325093000000000000000)
      constant := (958148177292331648351597482368715534670442015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279422353887178918833/50000000000000000000)
  centralHi := (558844707774357837667/100000000000000000000)
  directionLo := (280503295462695230641/50000000000000000000)
  directionHi := (561006590925390461283/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree131.table
  base := (9253658821027161585394257087933417913873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-534955821092020842762171378900000000000000)
      constant := (21227293710257865390258301851228103044899428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree131.table
  base := (37014635284005160007355809641929146722783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-24297181954464794408424244393200000000000000)
      constant := (972829593076485227639560034989251304422727115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280503295462695230641/50000000000000000000)
  centralHi := (561006590925390461283/100000000000000000000)
  directionLo := (281580087504447561351/50000000000000000000)
  directionHi := (563160175008895122703/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree132.table
  base := (38079971824133518499002824220021112926849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-179649557019873779978302865400000000000000)
      constant := (7183367960887439403209483002260063338780547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree132.table
  base := (38079971824047573640308260763596567632081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2719841269380166967617462632600000000000000)
      constant := (109735867109023090540841391736681845543443645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281580087504447561351/50000000000000000000)
  centralHi := (563160175008895122703/100000000000000000000)
  directionLo := (70663194359136051139/12500000000000000000)
  directionHi := (565305554873088409113/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree133.table
  base := (39157596940034947345810292064786001691811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-542941521027221837107645813500000000000000)
      constant := (21875353814730760329220461253545574015226299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree133.table
  base := (19578798469981787331457591388040466545739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-12329980447189105504345041496800000000000000)
      constant := (501263905001289077715903342507071388951024295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70663194359136051139/12500000000000000000)
  centralHi := (565305554873088409113/100000000000000000000)
  directionLo := (141860705893292416947/25000000000000000000)
  directionHi := (567442823573169667789/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree134.table
  base := (40247510622303613920047993526235078170101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-546934370994822334280383030800000000000000)
      constant := (22203043506377607878376775646286115703530909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree134.table
  base := (40247510622244345993010837276462595818691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-24841350364334919308823002293800000000000000)
      constant := (1017544611136745178413985389088087351306569855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141860705893292416947/25000000000000000000)
  centralHi := (567442823573169667789/100000000000000000000)
  directionLo := (569572072418418655807/100000000000000000000)
  directionHi := (8899563631537791497/1562500000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree135.table
  base := (20674856430799616450270087752483833183187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-183642406987474277151040082700000000000000)
      constant := (7511057652506266096402270135702402999099122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree135.table
  base := (10337428215387504873915941484403068950977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1390152213016201533830884533000000000000000)
      constant := (57370733743329235401081188734971276205587930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569572072418418655807/100000000000000000000)
  centralHi := (8899563631537791497/1562500000000000000)
  directionLo := (285846695508857218157/50000000000000000000)
  directionHi := (114338678203542887263/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree136.table
  base := (4246420364874634091626749981617376541733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-554920070930023328625857465400000000000000)
      constant := (22865742168071752391371391492345563888755970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree136.table
  base := (42464203648705478560002873095307588610727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-25204129304248335909088840894200000000000000)
      constant := (1047913598728405409620831915694319573387344435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285846695508857218157/50000000000000000000)
  centralHi := (114338678203542887263/20000000000000000000)
  directionLo := (573806867323539724981/100000000000000000000)
  directionHi := (286903433661769862491/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree137.table
  base := (43590982974730226639031663949231720830643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-558912920897623825798594682700000000000000)
      constant := (23200751137955337782916734179405585487475787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree137.table
  base := (8718196594939260012076887753926024353463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-25385518774205044209221760194400000000000000)
      constant := (1063265785178531854252211237890730199315762575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573806867323539724981/100000000000000000000)
  centralHi := (286903433661769862491/50000000000000000000)
  directionLo := (575912587674531827159/100000000000000000000)
  directionHi := (14397814691863295679/2500000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree138.table
  base := (44730050830692995576634463076422829948343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-187635256955074774323777300000000000000000)
      constant := (7846066622363277804471018208279268489845029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree138.table
  base := (1789202033226593160866281384221115123527/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2840767582684639167706075499400000000000000)
      constant := (119858862969635357872073670592768754513967875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575912587674531827159/100000000000000000000)
  centralHi := (14397814691863295679/2500000000000000000)
  directionLo := (289005318418319205287/50000000000000000000)
  directionHi := (23120425473465536423/4000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree139.table
  base := (22940703603964881543257533382315874752553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-566898620832824820144069117300000000000000)
      constant := (23878088355396895321077305354744185745545954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree139.table
  base := (9176281441581275968721346641003524670539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-25748297714118460809487598794800000000000000)
      constant := (1094305543369439111742100667430702137457841475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289005318418319205287/50000000000000000000)
  centralHi := (23120425473465536423/4000000000000000000)
  directionLo := (290050549021466809889/50000000000000000000)
  directionHi := (580101098042933619779/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree140.table
  base := (23522526048942484826829157689723778476817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-570891470800425317316806334600000000000000)
      constant := (24220416602799523470274349932415028012582706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree140.table
  base := (47045052097865558407399497184205668396763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-25929687184075169109620518095000000000000000)
      constant := (1109993115103229592314396349037603295700689015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290050549021466809889/50000000000000000000)
  centralHi := (580101098042933619779/100000000000000000000)
  directionLo := (582184053032147447539/100000000000000000000)
  directionHi := (29109202651607372377/5000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree141.table
  base := (48220985492148812934165566351347175411953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-191628106922675271496514517300000000000000)
      constant := (8188394869740676546636366858241541526235859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree141.table
  base := (9644197098426539959532219985978271525947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2901230739336875267750381932800000000000000)
      constant := (125088053547187083141647057597475111093338075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582184053032147447539/100000000000000000000)
  centralHi := (29109202651607372377/5000000000000000000)
  directionLo := (584259582085958825791/100000000000000000000)
  directionHi := (9129055970093106653/1562500000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree142.table
  base := (3088075461403361966721754879740243315111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-578877170735626311662280769200000000000000)
      constant := (24912392374590006316837158607232595037375984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree142.table
  base := (1976368295297616669462580727343824247987/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-26292466123988585709886356695400000000000000)
      constant := (1141703643830453287775862231030036220510868375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584259582085958825791/100000000000000000000)
  centralHi := (9129055970093106653/1562500000000000000)
  directionLo := (1172655528130201153/200000000000000000)
  directionHi := (586327764065100576501/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree143.table
  base := (2530485888033567765761417744304439746223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-582870020703226808835017986500000000000000)
      constant := (25262039898830296551611326568937299154320140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree143.table
  base := (50609717760660254148294445813806733008301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-26473855593945294010019275995600000000000000)
      constant := (1157726600817246186511807288012621726868361905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1172655528130201153/200000000000000000)
  centralHi := (586327764065100576501/100000000000000000000)
  directionLo := (294194338222161081483/50000000000000000000)
  directionHi := (588388676444322162967/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree144.table
  base := (51822516618808659197099834821151465912501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-195620956890275768669251734600000000000000)
      constant := (8538042393956988245570215134063454397737503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree144.table
  base := (51822516618799445559624357757149516024863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-2961693895989111367794688366200000000000000)
      constant := (130429039209091708229000216297151728221118835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294194338222161081483/50000000000000000000)
  centralHi := (588388676444322162967/100000000000000000000)
  directionLo := (295221197673127048703/50000000000000000000)
  directionHi := (590442395346254097407/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree145.table
  base := (53047603949005413978289538948734000589297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-590855720638427803180492421100000000000000)
      constant := (25968654223641268269921258296601106005303673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree145.table
  base := (53047603948997767300157318658918377081059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-26836634533858710610285114596000000000000000)
      constant := (1190107900021007459836935448196611942717828895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295221197673127048703/50000000000000000000)
  centralHi := (590442395346254097407/100000000000000000000)
  directionLo := (29624449778710794221/5000000000000000000)
  directionHi := (592488995574215884421/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree146.table
  base := (54284979743530832609493213429205077271679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-594848570606028300353229638400000000000000)
      constant := (26325621024071630067799426967612845695445111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree146.table
  base := (13571244935881121674573455361803912245861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-13509012001907709455209016948100000000000000)
      constant := (603233121115830748553804996107621168919147410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29624449778710794221/5000000000000000000)
  centralHi := (592488995574215884421/100000000000000000000)
  directionLo := (148632137661001876427/25000000000000000000)
  directionHi := (594528550644007505709/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree147.table
  base := (2776732199739033342528444544075091123601/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-199613806857876265841988951900000000000000)
      constant := (8895009194364537298727957902932005467416060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree147.table
  base := (55534643994775400679729870396379843778217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-3022157052641347467838994799600000000000000)
      constant := (135881819945634198180881384495707092970019765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148632137661001876427/25000000000000000000)
  centralHi := (594528550644007505709/100000000000000000000)
  directionLo := (298280566407361336659/50000000000000000000)
  directionHi := (596561132814722673319/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree148.table
  base := (28398298347637165655989086012411989099907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-602834270541229294698704073000000000000000)
      constant := (27046873900639888486568752926623415803798326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree148.table
  base := (11359319339053992273445474719122847163529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-27380802943728835510683872496600000000000000)
      constant := (1239518311855116697507621425711103765506146225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298280566407361336659/50000000000000000000)
  centralHi := (596561132814722673319/100000000000000000000)
  directionLo := (598586813118620391179/100000000000000000000)
  directionHi := (29929340655931019559/5000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree149.table
  base := (14517709459413027883768039817135914262763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-606827120508829791871441290300000000000000)
      constant := (27411159976644222408826224542779392913459468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree149.table
  base := (58070837837648485456016997855582035718877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-27562192413685543810816791796800000000000000)
      constant := (1256212039261907567008245308022780724466145185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598586813118620391179/100000000000000000000)
  centralHi := (29929340655931019559/5000000000000000000)
  directionLo := (24024226455603590501/4000000000000000000)
  directionHi := (300302830695044881263/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree150.table
  base := (29678683707336226501292007860242638003027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-203606656825476763014726169200000000000000)
      constant := (9259295270347146557433629008411455828018162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree150.table
  base := (2967868370733472215029003557891379384497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1541310104646791783941650616500000000000000)
      constant := (70723197873785976279353835846051120723023650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24024226455603590501/4000000000000000000)
  centralHi := (300302830695044881263/50000000000000000000)
  directionLo := (18831804571679420599/3125000000000000000)
  directionHi := (602617746293741459169/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree151.table
  base := (15164046354802332031768316339883697514729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-614812820444030786216915724900000000000000)
      constant := (28147051403767406028705776089798313110530244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree151.table
  base := (60656185419206831797468315128508215107733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-27924971353598960411082630397200000000000000)
      constant := (1289934879250950683096096084588115827118631865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18831804571679420599/3125000000000000000)
  centralHi := (602617746293741459169/100000000000000000000)
  directionLo := (604623135351657822917/100000000000000000000)
  directionHi := (302311567675828911459/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree152.table
  base := (15491822961062419602303027700151006014287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-618805670411631283389652942200000000000000)
      constant := (28518656754759003951546941560005436216514332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree152.table
  base := (61967291844247607286749463847313787801337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-28106360823555668711215549697400000000000000)
      constant := (1306963991827476615744153858402642084059541485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604623135351657822917/100000000000000000000)
  centralHi := (302311567675828911459/50000000000000000000)
  directionLo := (151655473742458048859/25000000000000000000)
  directionHi := (606621894969832195437/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree153.table
  base := (3164534334144546454558697450718981340367/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-207599506793077260187463386500000000000000)
      constant := (9630900621318036756001314669530638880422020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree153.table
  base := (12658137336577842164573103012826204349587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-3143083365945819667927607666400000000000000)
      constant := (147122766606103314910510152862355895978657075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151655473742458048859/25000000000000000000)
  centralHi := (606621894969832195437/100000000000000000000)
  directionLo := (3803838065398917291/625000000000000000)
  directionHi := (608614090463826766561/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree154.table
  base := (32313184964169286877116962488821666167979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-626791370346832277735127376800000000000000)
      constant := (29269186731291574420308259740348789991023622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree154.table
  base := (64626369928337148285238275959339274639799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-28469139763469085311481388297800000000000000)
      constant := (1341357602130558568328574468571852406229118595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3803838065398917291/625000000000000000)
  centralHi := (608614090463826766561/100000000000000000000)
  directionLo := (152649946520919247169/25000000000000000000)
  directionHi := (610599786083676988677/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree155.table
  base := (3298717078695191321253346667678189474059/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-630784220314432774907864594100000000000000)
      constant := (29648111356711197334699962807244574105330620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree155.table
  base := (13194868314780528782150855129819793206389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-28650529233425793611614307598000000000000000)
      constant := (1358722099851653863962042181126635081242937725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152649946520919247169/25000000000000000000)
  centralHi := (610599786083676988677/100000000000000000000)
  directionLo := (153144761259517355719/25000000000000000000)
  directionHi := (612579045038069422877/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree156.table
  base := (2104206300406291839470450605465760015281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-211592356760677757360200603800000000000000)
      constant := (10009825246717903625671162072124712961466976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree156.table
  base := (67334601613000357935111016521061167693619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-3203546522598055767971914099800000000000000)
      constant := (152910932512838739832272444654727752546212855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153144761259517355719/25000000000000000000)
  centralHi := (612579045038069422877/100000000000000000000)
  directionLo := (614551929517818757677/100000000000000000000)
  directionHi := (307275964758909378839/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree157.table
  base := (68707150039146980801936101957655516153791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-638769920249633769253339028700000000000000)
      constant := (30413279881560757874852487437981399645384119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree157.table
  base := (17176787509786541782139066416498779322661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-14506654086669605105940073099200000000000000)
      constant := (696893240209808441002877138270679011251355410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614551929517818757677/100000000000000000000)
  centralHi := (307275964758909378839/50000000000000000000)
  directionLo := (154129625179667167573/25000000000000000000)
  directionHi := (616518500718668670293/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree158.table
  base := (17522996711488920253514391508700370148399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-642762770217234266426076246000000000000000)
      constant := (30799523780874872687168076736463213325342364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree158.table
  base := (700919868459550061044086922691875513371/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-14597348821647959256006532749300000000000000)
      constant := (705743181630636291513171533046550479145762750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154129625179667167573/25000000000000000000)
  centralHi := (616518500718668670293/100000000000000000000)
  directionLo := (618478818863440180611/100000000000000000000)
  directionHi := (154619704715860045153/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree159.table
  base := (71489112027139327154820518283859801489737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-215585206728278254532937821100000000000000)
      constant := (10396069146013154100952956490639079404469211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree159.table
  base := (71489112027138767366392545161316500693071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-3264009679250291868016220533200000000000000)
      constant := (158810893459774342001802965702689242531188195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618478818863440180611/100000000000000000000)
  centralHi := (154619704715860045153/25000000000000000000)
  directionLo := (155108235805887544157/25000000000000000000)
  directionHi := (620432943223550176629/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree160.table
  base := (72898525576504722429255832063451123509143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-650748470152435260771550680600000000000000)
      constant := (31579330852998787950770143504571060111582287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree160.table
  base := (36449262788252129071854693602542755405057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-14778738291604667556139452049500000000000000)
      constant := (723610757023599061951615892597029815939048085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155108235805887544157/25000000000000000000)
  centralHi := (620432943223550176629/100000000000000000000)
  directionLo := (622380932139921864341/100000000000000000000)
  directionHi := (311190466069960932171/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree161.table
  base := (74320227487951597202330753093787532099949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-654741320120035757944287897900000000000000)
      constant := (31972894025697947204186604045906587788899541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree161.table
  base := (37160113743975606070639031947867875450259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-14869433026583021706205911699600000000000000)
      constant := (732628390993244556418925240064121489557354895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622380932139921864341/100000000000000000000)
  centralHi := (311190466069960932171/50000000000000000000)
  directionLo := (624322843043308012793/100000000000000000000)
  directionHi := (312161421521654006397/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree162.table
  base := (75754217755470673750057093715796195513963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-219578056695878751705675038400000000000000)
      constant := (10789632318694285521197452468997388586541889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree162.table
  base := (75754217755470354407046000357719018596049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (1166)
      previous := (0)
      next := (814)
      square := (17112214146859273597445217000000000000000)
      linear := (-3324472835902527968060526966600000000000000)
      constant := (164822649439267587607166831478017355836822205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624322843043308012793/100000000000000000000)
  centralHi := (312161421521654006397/50000000000000000000)
  directionLo := (626258732474047023567/100000000000000000000)
  directionHi := (39141170779627938973/6250000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree163.table
  base := (9650062046642722802501561575430120964199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-662727020055236752289762332500000000000000)
      constant := (32767339644100234502115602335893468709422328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree163.table
  base := (38600248186570758794501289761326880070139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2025000000000000000000000000000000000000000
      center := (5247)
      previous := (0)
      next := (3663)
      square := (77004963660866731188503476500000000000000)
      linear := (-15050822496539730006338830999800000000000000)
      constant := (750831351472778991502810247401552386428406295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626258732474047023567/100000000000000000000)
  centralHi := (39141170779627938973/6250000000000000000)
  directionLo := (15704716402531776291/2500000000000000000)
  directionHi := (628188656101271051641/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree164.table
  base := (3932953166756601376891339654195635840253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-666719870022837249462499549800000000000000)
      constant := (33168222089697584958687007422555214451245540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree164.table
  base := (78659063335131807921785738185889058743207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-30283034463036168312810581299800000000000000)
      constant := (1520033355960575874486235879033205068790998835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15704716402531776291/2500000000000000000)
  centralHi := (628188656101271051641/100000000000000000000)
  directionLo := (315056334370792319461/50000000000000000000)
  directionHi := (630112668741584638923/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree165.table
  base := (40064959317847000730385049714797036524887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-223570906663479248878412255700000000000000)
      constant := (11190514764274393754840667868476282219149322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree165.table
  base := (4006495931784690967339628869973822704433/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1692467996277382034052416700000000000000000)
      constant := (85473100222007459080700747884363220216994850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315056334370792319461/50000000000000000000)
  centralHi := (630112668741584638923/100000000000000000000)
  directionLo := (79003853047153948897/12500000000000000000)
  directionHi := (632030824377231591177/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree166.table
  base := (81613062269164045241043878919689713974989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-674705569958038243807973984400000000000000)
      constant := (33977306253426050489090404090027207425774901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree166.table
  base := (81613062269163894230700149979528408459267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-30645813402949584913076419900200000000000000)
      constant := (1557110047049939368563257449849629005426003135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79003853047153948897/12500000000000000000)
  centralHi := (632030824377231591177/100000000000000000000)
  directionLo := (158485794043441782901/25000000000000000000)
  directionHi := (126788635234753426321/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree167.table
  base := (41554247114980277209968934342715858819303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-678698419925638740980711201700000000000000)
      constant := (34385507971455958192263816510531385458747454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree167.table
  base := (83108494229960429205473853988023225059527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-30827202872906293213209339200400000000000000)
      constant := (1575816085119730640454113829041579406149108435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158485794043441782901/25000000000000000000)
  centralHi := (126788635234753426321/20000000000000000000)
  directionLo := (635849776497251698351/100000000000000000000)
  directionHi := (39740611031078231147/6250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree168.table
  base := (42308107256291164264921869041068129589893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (77)
      previous := (0)
      next := (55)
      square := (1140814276457284906496347800000000000000)
      linear := (-227563756631079746051149473000000000000000)
      constant := (11598716482287797856611255297046408777539358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree168.table
  base := (42308107256291112354222432535922913675079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (583)
      previous := (0)
      next := (407)
      square := (8556107073429636798722608500000000000000)
      linear := (-1722699574603500084074569916700000000000000)
      constant := (88590773233515560739016762535076531115378555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell226.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635849776497251698351/100000000000000000000)
  centralHi := (39740611031078231147/6250000000000000000)
  directionLo := (159437669232745529277/25000000000000000000)
  directionHi := (637750676930982117109/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree169.table
  base := (21534055777901740733600614516454693833957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (231)
      previous := (0)
      next := (165)
      square := (3422442829371854719489043400000000000000)
      linear := (-686684119860839735326185636300000000000000)
      constant := (35209230679599554980073020970454868978022452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 53
  qDenominator := 90
  table := BinomialMassData.Q53_90.Degree169.table
  base := (86136223111606876854054664370404765454331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4050000000000000000000000000000000000000000
      center := (10494)
      previous := (0)
      next := (7326)
      square := (154009927321733462377006953000000000000000)
      linear := (-31189981812819709813475177800800000000000000)
      constant := (1613563546298391653534169939480483930009004055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_90.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell226.Kernel169
