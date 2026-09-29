import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell231.Parameters
import ForestUnimodality.BinomialMassData.Q63_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q63_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q63_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q63_103.Batch150_199
import ForestUnimodality.BinomialMassData.Q129_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q129_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q129_209.Batch100_149
import ForestUnimodality.BinomialMassData.Q129_209.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree000.table
  base := (31723024945150480716193897/2500000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (2079)
      previous := (0)
      next := (1320)
      square := (34288478701029531103827707690000000000000)
      linear := (-95835543897565203946831146850000000000000)
      constant := (13069886277401998055071885564000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree000.table
  base := (31723024945150480716193897/2500000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (387)
      previous := (0)
      next := (240)
      square := (6325059177859816417210936370000000000000)
      linear := (-17678401301492610436794095050000000000000)
      constant := (2410949895831436534430736172000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree001.table
  base := (70515111716778703885630326610236581018431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-14191409337778936925605899294490000000000000)
      constant := (755453731041321646390245139704419888024534479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree001.table
  base := (3500313264105287381477317731357278951047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-58593162538897670386234261938010000000000000)
      constant := (3088569078380729976679120252719726037213680140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48606411862967633061/100000000000000000000)
  directionHi := (24303205931483816531/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree002.table
  base := (1309668178532988201755412244447821211653/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-18511757654108657844688190463430000000000000)
      constant := (461976995414779390410612686325681927501653664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree002.table
  base := (41400066865359857506070130550574060448953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-76543680485663829378278899356070000000000000)
      constant := (1880726636224423165194651475833245534470715993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/100000000000000000000)
  centralHi := (24303205931483816531/50000000000000000000)
  directionLo := (8592480859362665481/12500000000000000000)
  directionHi := (68739846874901323849/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree003.table
  base := (5306127097823059594072709902948835724939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-22832105970438378763770481632370000000000000)
      constant := (311467873852891940884021765560400991029389255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree003.table
  base := (26127587791372612219659083010493011192171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-94494198432429988370323536774130000000000000)
      constant := (1266393894971658319364216905988065221885221451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8592480859362665481/12500000000000000000)
  centralHi := (68739846874901323849/100000000000000000000)
  directionLo := (84188774920278546287/100000000000000000000)
  directionHi := (5261798432517409143/6250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree004.table
  base := (1765600545177511719824934748261317863789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-27152454286768099682852772801310000000000000)
      constant := (232603464059584954053911055567163212169375010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree004.table
  base := (17353890950407981318467887505338086827807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-112444716379196147362368174192190000000000000)
      constant := (947013966732055893020760923631352970725437567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/100000000000000000000)
  centralHi := (5261798432517409143/6250000000000000000)
  directionLo := (48606411862967633061/50000000000000000000)
  directionHi := (97212823725935266123/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree005.table
  base := (12122992658596461275431507757638217954101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-31472802603097820601935063970250000000000000)
      constant := (191832814754527122387870738180283854275057509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree005.table
  base := (2973957692274939005935304424888465811/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-130395234325962306354412811610250000000000000)
      constant := (783543869715406520499472119099712300361164000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/50000000000000000000)
  centralHi := (97212823725935266123/100000000000000000000)
  directionLo := (6792952566746738769/6250000000000000000)
  directionHi := (21737448213589564061/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree006.table
  base := (8412350761131048376758699071218722556787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-35793150919427541521017355139190000000000000)
      constant := (173038241427030624002870339971179427604953283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree006.table
  base := (8237686109052087459355564236950990190371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-148345752272728465346457449028310000000000000)
      constant := (709775388875441127042399480205436202505595651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/6250000000000000000)
  centralHi := (21737448213589564061/20000000000000000000)
  directionLo := (3720653352869806377/3125000000000000000)
  directionHi := (23812181458366760813/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree007.table
  base := (5764406266996549943396620739010069677927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-40113499235757262440099646308130000000000000)
      constant := (168160367996411335218236764979637829213127543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree007.table
  base := (5626845615787528950702561384278043422409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-166296270219494624338502086446370000000000000)
      constant := (692833707637230364455974983354369214734247529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3720653352869806377/3125000000000000000)
  centralHi := (23812181458366760813/20000000000000000000)
  directionLo := (64300238956296042183/50000000000000000000)
  directionHi := (128600477912592084367/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree008.table
  base := (944946025963203553391888118266744205539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-44433847552086983359181937477070000000000000)
      constant := (172962224320212585993270178670847557106253004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree008.table
  base := (917363009839738478972360810889472260459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-184246788166260783330546723864430000000000000)
      constant := (715514747465833796516540721356972151236438316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64300238956296042183/50000000000000000000)
  centralHi := (128600477912592084367/100000000000000000000)
  directionLo := (8592480859362665481/6250000000000000000)
  directionHi := (137479693749802647697/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree009.table
  base := (69851348341522199132513556155246023331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-48754195868416704278264228646010000000000000)
      constant := (185075445305737449511306060450452161968594528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree009.table
  base := (2145770430529732407281734857989257729943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-202197306113026942322591361282490000000000000)
      constant := (768220266043646190481475193625208766901640183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8592480859362665481/6250000000000000000)
  centralHi := (137479693749802647697/100000000000000000000)
  directionLo := (145819235588902899183/100000000000000000000)
  directionHi := (9113702224306431199/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree010.table
  base := (997413221015014170544511693042638417141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-53074544184746425197346519814950000000000000)
      constant := (203085106764191265716074591553989350967448869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree010.table
  base := (36979637268522112999001585450531414591/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-220147824059793101314635998700550000000000000)
      constant := (845214517481418028855354452654116568018736775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145819235588902899183/100000000000000000000)
  centralHi := (9113702224306431199/6250000000000000000)
  directionLo := (38426742593801460623/25000000000000000000)
  directionHi := (153706970375205842493/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree011.table
  base := (-464994407215457646389109134299345309/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-57394892501076146116428810983890000000000000)
      constant := (226090567163208786020392038244088729824672760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree011.table
  base := (-976094794951670361205334762452494681/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-1967754892616192233939509389410000000000000)
      constant := (7792077296465142769409943568940371953612720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38426742593801460623/25000000000000000000)
  centralHi := (153706970375205842493/100000000000000000000)
  directionLo := (8060461527747162311/5000000000000000000)
  directionHi := (161209230554943246221/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree012.table
  base := (-869797684140174948582256079076119141373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-61715240817405867035511102152830000000000000)
      constant := (253487093991162916882035704336961452029173843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree012.table
  base := (-229562585927157287866480017770117937831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-256048859953325419298725273536670000000000000)
      constant := (1058642177158394778438243609948453913430416356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8060461527747162311/5000000000000000000)
  centralHi := (161209230554943246221/100000000000000000000)
  directionLo := (84188774920278546287/50000000000000000000)
  directionHi := (6735101993622283703/4000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree013.table
  base := (-63841412785558711447271138119658194837/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-66035589133735587954593393321770000000000000)
      constant := (284851867493447056990158794845393655274356675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree013.table
  base := (-1635386082073943131971368965733836590319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-273999377900091578290769910954730000000000000)
      constant := (1190896451073947519242973802042800283898275761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/50000000000000000000)
  centralHi := (6735101993622283703/4000000000000000000)
  directionLo := (43813227572062732337/25000000000000000000)
  directionHi := (175252910288250929349/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree014.table
  base := (-2225978044425729095246509844030727038987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-70355937450065308873675684490710000000000000)
      constant := (319880776848414677622392767780898016843386917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree014.table
  base := (-2257825558228057536755293267272196804737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-291949895846857737282814548372790000000000000)
      constant := (1338366658711649269240986140639863171372283103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43813227572062732337/25000000000000000000)
  centralHi := (175252910288250929349/100000000000000000000)
  directionLo := (181868539991649377867/100000000000000000000)
  directionHi := (45467134997912344467/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree015.table
  base := (-695157862576059739842176159166250270773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-74676285766395029792757975659650000000000000)
      constant := (358350973732619475871907396378621003509476972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree015.table
  base := (-56126249419295444387677691822686660629/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-309900413793623896274859185790850000000000000)
      constant := (1500146694564488057028655809785661198853232550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181868539991649377867/100000000000000000000)
  centralHi := (45467134997912344467/25000000000000000000)
  directionLo := (188251823664172267531/100000000000000000000)
  directionHi := (47062955916043066883/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree016.table
  base := (-3275571367373827270295228471325558337061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-78996634082724750711840266828590000000000000)
      constant := (400097214164537660917160183059227151602119851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree016.table
  base := (-3296205834234964780001051290997159396709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-327850931740390055266903823208910000000000000)
      constant := (1675565661544075598154096748683233080392354171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188251823664172267531/100000000000000000000)
  centralHi := (47062955916043066883/25000000000000000000)
  directionLo := (48606411862967633061/25000000000000000000)
  directionHi := (38885129490374106449/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree017.table
  base := (-3722432280409001635123700898131481062263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-83316982399054471630922557997530000000000000)
      constant := (444996067895196481554452482015503117410451833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree017.table
  base := (-934738922435165619575569459814425917663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-345801449687156214258948460626970000000000000)
      constant := (1864123410378825639886550500093804245962249988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/25000000000000000000)
  centralHi := (38885129490374106449/20000000000000000000)
  directionLo := (200409370193290840143/100000000000000000000)
  directionHi := (12525585637080677509/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree018.table
  base := (-1032485876703594132791782353826081731679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-87637330715384192550004849166470000000000000)
      constant := (492954925596250382793970596698816395634469956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree018.table
  base := (-2071566597934263984706236730624347849989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-363751967633922373250993098045030000000000000)
      constant := (2065445544299250370787505904145615723129260982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200409370193290840143/100000000000000000000)
  centralHi := (12525585637080677509/6250000000000000000)
  directionLo := (25777442578087996443/12500000000000000000)
  directionHi := (41243908124940794309/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree019.table
  base := (-2252336140333671909794856187253565464863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-91957679031713913469087140335410000000000000)
      constant := (543904115481372314380623546796373847966536866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree019.table
  base := (-4515170279073821401743760239904198900147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-20089604504246764854896722919110000000000000)
      constant := (119960584753992503806009108217580246728562047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25777442578087996443/12500000000000000000)
  centralHi := (41243908124940794309/20000000000000000000)
  directionLo := (211870437318792477957/100000000000000000000)
  directionHi := (105935218659396238979/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree020.table
  base := (-4851567246996492879548338772437984267851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-96278027348043634388169431504350000000000000)
      constant := (597791137375453971590935896942205424902368741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree020.table
  base := (-2429950312171849175020802492701141915837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-399653003527454691235082372881150000000000000)
      constant := (2505328968264723301806095220323642839948648006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211870437318792477957/100000000000000000000)
  centralHi := (105935218659396238979/50000000000000000000)
  directionLo := (6792952566746738769/3125000000000000000)
  directionHi := (217374482135895640609/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree021.table
  base := (-5174360992335630297568396635371646430089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-100598375664373355307251722673290000000000000)
      constant := (654576392267958200348459805565562203023185799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree021.table
  base := (-2590479985113019492792429674682318561377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-417603521474220850227127010299210000000000000)
      constant := (2743520305420337605501640877719983285840982526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/3125000000000000000)
  centralHi := (217374482135895640609/100000000000000000000)
  directionLo := (22274256162224868701/10000000000000000000)
  directionHi := (222742561622248687011/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree022.table
  base := (-5475870500778044537473641578713366164943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-104918723980703076226334013842230000000000000)
      constant := (714229994774639303340489049342609898356119713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree022.table
  base := (-5481084407045400312771434783407964920037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-3599620160504024869579930972870000000000000)
      constant := (24741368649844905032162850067809724663866643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22274256162224868701/10000000000000000000)
  centralHi := (222742561622248687011/100000000000000000000)
  directionLo := (113992140115265945343/50000000000000000000)
  directionHi := (227984280230531890687/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree023.table
  base := (-1151644497304118919357474419225088958767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-109239072297032797145416305011170000000000000)
      constant := (776729382584582803462298954554085156182204485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree023.table
  base := (-5762333620618121563157344580515670919713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-453504557367753168211216285135330000000000000)
      constant := (3255794902761267498002688945127814978556016447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113992140115265945343/50000000000000000000)
  centralHi := (227984280230531890687/100000000000000000000)
  directionLo := (1165540811237707529/500000000000000000)
  directionHi := (233108162247541505801/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree024.table
  base := (-1204604574211376468953056882585126061549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-113559420613362518064498596180110000000000000)
      constant := (842057518476663078482955839945591988065133295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree024.table
  base := (-1205251678731691238872570413297070950971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-471455075314519327203260922553390000000000000)
      constant := (3529720454070698267552282416154333218953178745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1165540811237707529/500000000000000000)
  centralHi := (233108162247541505801/100000000000000000000)
  directionLo := (3720653352869806377/1562500000000000000)
  directionHi := (238121814583667608129/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree025.table
  base := (-783935558718613853878742886566968566583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-117879768929692238983580887349050000000000000)
      constant := (910201535692704638049013918063788243816967624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree025.table
  base := (-6274026474462434807027100671064751535567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-489405593261285486195305559971450000000000000)
      constant := (3815431252146206904873966847129720588174897873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3720653352869806377/1562500000000000000)
  centralHi := (238121814583667608129/100000000000000000000)
  directionLo := (48606411862967633061/20000000000000000000)
  directionHi := (121516029657419082653/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree026.table
  base := (-6504523291618837077227434518678557739349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-122200117246021959902663178517990000000000000)
      constant := (981151716292991418317829858463759180943246459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree026.table
  base := (-3253258622943711207564846281624850346857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-507356111208051645187350197389510000000000000)
      constant := (4112888884665200848792099235710069823997878766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/20000000000000000000)
  centralHi := (121516029657419082653/50000000000000000000)
  directionLo := (12392252128749989333/5000000000000000000)
  directionHi := (247845042574999786661/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree027.table
  base := (-6722831212056952833789944043551671187743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-126520465562351680821745469686930000000000000)
      constant := (1054900720171507814109068606744040320369234513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree027.table
  base := (-268975718643849770193369702655688049329/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-525306629154817804179394834807570000000000000)
      constant := (4422064423528869730165816722796542257931498775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12392252128749989333/5000000000000000000)
  centralHi := (247845042574999786661/100000000000000000000)
  directionLo := (252566324760835638861/100000000000000000000)
  directionHi := (126283162380417819431/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree028.table
  base := (-6926930835301829393730051675735534487507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-130840813878681401740827760855870000000000000)
      constant := (1131443003019886822575159701593601714622038237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree028.table
  base := (-866019049470015221492396328718371989981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-543257147101583963171439472225630000000000000)
      constant := (4742936082372333925021198526585742344845119512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252566324760835638861/100000000000000000000)
  centralHi := (126283162380417819431/50000000000000000000)
  directionLo := (257200955825184168733/100000000000000000000)
  directionHi := (128600477912592084367/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree029.table
  base := (-3558608460236822406329128656073044444017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-135161162195011122659910052024810000000000000)
      constant := (1210774376838622474724131349606062142986847294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree029.table
  base := (-7118171173915604958745430169238735867041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-561207665048350122163484109643690000000000000)
      constant := (5075487452906837893144546700916662778591782079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200955825184168733/100000000000000000000)
  centralHi := (128600477912592084367/50000000000000000000)
  directionLo := (261753538565538362481/100000000000000000000)
  directionHi := (130876769282769181241/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree030.table
  base := (-7293987665901201257051870612610110629039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-139481510511340843578992343193750000000000000)
      constant := (1292891678041644508371825772600319336336525249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree030.table
  base := (-7294732220177552346460858841520874586819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-579158182995116281155528747061750000000000000)
      constant := (5419706176920684999034171689109026677173159261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261753538565538362481/100000000000000000000)
  centralHi := (130876769282769181241/50000000000000000000)
  directionLo := (16639267635458798599/6250000000000000000)
  directionHi := (53245656433468155517/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree031.table
  base := (-372873416818372530467535440421715327943/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-143801858827670564498074634362690000000000000)
      constant := (1377792516794870586997438949569440441717054260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree031.table
  base := (-3729024314219828073322042743554064506517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-597108700941882440147573384479810000000000000)
      constant := (5775582946259504873196981024780309816581661846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16639267635458798599/6250000000000000000)
  centralHi := (53245656433468155517/20000000000000000000)
  directionLo := (270629047775669602319/100000000000000000000)
  directionHi := (3382863097195870029/1250000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree032.table
  base := (-9509786385247144768868608659085028037/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-148122207144000285417156925531630000000000000)
      constant := (1465475087697665359471735800185093550044373600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree032.table
  base := (-3804140453545377470069397968668807836509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-615059218888648599139618021897870000000000000)
      constant := (6143110749756364657583141667131875609786900742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270629047775669602319/100000000000000000000)
  centralHi := (3382863097195870029/1250000000000000000)
  directionLo := (274959387499605295393/100000000000000000000)
  directionHi := (137479693749802647697/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree033.table
  base := (-7745198547576898614360742303756987589097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-152442555460330006336239216700570000000000000)
      constant := (1555938026791373203234246461664022118667269927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree033.table
  base := (-7745549962122252615959008095987839924913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-5231485428391857505220352556330000000000000)
      constant := (53903176083608709412534151240568389787106407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274959387499605295393/100000000000000000000)
  centralHi := (137479693749802647697/50000000000000000000)
  directionLo := (11168903118809871129/4000000000000000000)
  directionHi := (139611288985123389113/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree034.table
  base := (-7869673790820937261295628701549139075383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-156762903776659727255321507869510000000000000)
      constant := (1649180303556818329346721657927685183549261753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree034.table
  base := (-7869946874450905283735817001659459872313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-650960254782180917123707296733990000000000000)
      constant := (6913099636834847593572657061329893133317495847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11168903118809871129/4000000000000000000)
  centralHi := (139611288985123389113/50000000000000000000)
  directionLo := (141710824677001105647/50000000000000000000)
  directionHi := (56684329870800442259/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree035.table
  base := (-3990664116840840751854490776019086430669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-161083252092989448174403799038450000000000000)
      constant := (1745201139338469363834651088484427024114065158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree035.table
  base := (-159630805261645014069450113811039455067/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-668910772728947076115751934152050000000000000)
      constant := (7315553744564165026656512544490999278160918650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141710824677001105647/50000000000000000000)
  centralHi := (56684329870800442259/20000000000000000000)
  directionLo := (287559410551516158729/100000000000000000000)
  directionHi := (28755941055151615873/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree036.table
  base := (-161604346784465726770205695517043861607/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-165403600409319169093486090207390000000000000)
      constant := (1843999945728678686335822038420304083610566850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree036.table
  base := (-8080381830230618824064619483466349777819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-686861290675713235107796571570110000000000000)
      constant := (7729644370900181991670492434434186375355088261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287559410551516158729/100000000000000000000)
  centralHi := (28755941055151615873/10000000000000000000)
  directionLo := (291638471177805798367/100000000000000000000)
  directionHi := (9113702224306431199/3125000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree037.table
  base := (-408319151231940860035269866317486186273/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-169723948725648890012568381376330000000000000)
      constant := (1945576278027945065650257350099135780996594860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree037.table
  base := (-4083255268652174230350604271325895812463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-704811808622479394099841208988170000000000000)
      constant := (8155369813969620840828323831022247090031607394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291638471177805798367/100000000000000000000)
  centralHi := (9113702224306431199/3125000000000000000)
  directionLo := (9239414400384450063/3125000000000000000)
  directionHi := (295661260812302402017/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree038.table
  base := (-41199284873605906382629801849245748041/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-174044297041978610931650672545270000000000000)
      constant := (2049929800092300549439225542387450371806606200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree038.table
  base := (-1029994468727070282302524299489208455777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-38040122451012923846941360337170000000000000)
      constant := (452248883739868571782742383368374478081349416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9239414400384450063/3125000000000000000)
  centralHi := (295661260812302402017/100000000000000000000)
  directionLo := (299630045922155050941/100000000000000000000)
  directionHi := (149815022961077525471/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree039.table
  base := (-83006631446190168904710950729779392999/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-178364645358308331850732963714210000000000000)
      constant := (2157060257781573233718115438828497041967360900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree039.table
  base := (-2075184901452011690168545497953071808333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-740712844516011712083930483824290000000000000)
      constant := (9041720335152068463797283556606727481360824908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299630045922155050941/100000000000000000000)
  centralHi := (149815022961077525471/50000000000000000000)
  directionLo := (75886736198390256521/25000000000000000000)
  directionHi := (60709388958712205217/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree040.table
  base := (-8348819650245690570747533436514249706389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-182684993674638052769815254883150000000000000)
      constant := (2266967458904038212989181819626020324864919099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree040.table
  base := (-8348878799507413897503488880415665465627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-758663362462777871075975121242350000000000000)
      constant := (9502343717032717642887767537940563316795947013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75886736198390256521/25000000000000000000)
  centralHi := (60709388958712205217/20000000000000000000)
  directionLo := (61482788150082336997/20000000000000000000)
  directionHi := (153706970375205842493/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree041.table
  base := (-4192170098085952026849235946263692724169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-187005341990967773688897546052090000000000000)
      constant := (2379651258067904912531559713832196967778582158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree041.table
  base := (-8384385924614151236012394948815322287541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-776613880409544030068019758660410000000000000)
      constant := (9974598386594063084724875178252577907157921579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61482788150082336997/20000000000000000000)
  centralHi := (153706970375205842493/50000000000000000000)
  directionLo := (31123289389441159553/10000000000000000000)
  directionHi := (311232893894411595531/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree042.table
  base := (-1681447030834273154541592112872368538331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-191325690307297494607979837221030000000000000)
      constant := (2495111545239026059575477733688465210884232105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree042.table
  base := (-1681454097187889458981677073735810973711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-794564398356310189060064396078470000000000000)
      constant := (10458483928656447263622944817759150204286649045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31123289389441159553/10000000000000000000)
  centralHi := (311232893894411595531/100000000000000000000)
  directionLo := (63001110312781792201/20000000000000000000)
  directionHi := (157502775781954480503/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree043.table
  base := (-8417512377898306335865928751153891580677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-195646038623627215527062128389970000000000000)
      constant := (2613348237097983921599709819260288364220597707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree043.table
  base := (-1052192457661443959162780973127121949483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-812514916303076348052109033496530000000000000)
      constant := (10954000029686028028843218141338593488997064616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63001110312781792201/20000000000000000000)
  centralHi := (157502775781954480503/50000000000000000000)
  directionLo := (318733557678313734091/100000000000000000000)
  directionHi := (79683389419578433523/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree044.table
  base := (-8415177818260355308120413612188625742283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-199966386939956936446144419558910000000000000)
      constant := (2734361270511599456549722244324810869500119653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree044.table
  base := (-8415198875273406051357555320248566279959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-6863350696279690140860774139790000000000000)
      constant := (94720218617609291610367521582070267572934801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318733557678313734091/100000000000000000000)
  centralHi := (79683389419578433523/25000000000000000000)
  directionLo := (322418461109886492441/100000000000000000000)
  directionHi := (161209230554943246221/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree045.table
  base := (-2100058997063153834567782034833427946589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-204286735256286657365226710727850000000000000)
      constant := (2858150597601507620424398853751308651658549196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree045.table
  base := (-4200126115716783063197804288690849822749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-848415952196608666036198308332650000000000000)
      constant := (11979923018543431570242008996394889977785001862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322418461109886492441/100000000000000000000)
  centralHi := (161209230554943246221/50000000000000000000)
  directionLo := (20378857700240216307/6250000000000000000)
  directionHi := (326061723203843460913/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree046.table
  base := (-8372690314086497222689722212269468365263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-208607083572616378284309001896790000000000000)
      constant := (2984716182019031556085032813966253210112924833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree046.table
  base := (-837270283774438188597302131951521083079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-866366470143374825028242945750710000000000000)
      constant := (12510329591364809665199374350445836075700262010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20378857700240216307/6250000000000000000)
  centralHi := (326061723203843460913/100000000000000000000)
  directionLo := (32966472455034109983/10000000000000000000)
  directionHi := (329664724550341099831/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree047.table
  base := (-8332543400434230068314859617371116299957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-212927431888946099203391293065730000000000000)
      constant := (3114057996131203584936111840859989827173756187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree047.table
  base := (-8332553051745721504756400397213137177833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-884316988090140984020287583168770000000000000)
      constant := (13052366068215159587988954119743852954935076727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32966472455034109983/10000000000000000000)
  centralHi := (329664724550341099831/100000000000000000000)
  directionLo := (166614385548670969579/50000000000000000000)
  directionHi := (333228771097341939159/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree048.table
  base := (-1034974653850320322581830752209283671431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-217247780205275820122473584234670000000000000)
      constant := (3246176018895000609960900441453373676238308168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree048.table
  base := (-8279804665189121319086761056596255126819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-902267506036907143012332220586830000000000000)
      constant := (13606032370828982479903036417323138979805419261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166614385548670969579/50000000000000000000)
  centralHi := (333228771097341939159/100000000000000000000)
  directionLo := (84188774920278546287/25000000000000000000)
  directionHi := (336755099681114185149/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree049.table
  base := (-8214453318907443357555330970070584225221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-221568128521605541041555875403610000000000000)
      constant := (3381070234251410132484847754197341171954630411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree049.table
  base := (-256701845097488719607608696416298602397/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-920218023983673302004376858004890000000000000)
      constant := (14171328439579745175614343664347849143958292576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/25000000000000000000)
  centralHi := (336755099681114185149/100000000000000000000)
  directionLo := (85061220760193357857/25000000000000000000)
  directionHi := (340244883040773431429/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree050.table
  base := (-8136512823037851570360990399340403795973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-225888476837935261960638166572550000000000000)
      constant := (3518740629912144372479164477605897656128522443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree050.table
  base := (-8136517228644389128953414638649353040883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-938168541930439460996421495422950000000000000)
      constant := (14748254228903485806686515377541657609821189677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85061220760193357857/25000000000000000000)
  centralHi := (340244883040773431429/100000000000000000000)
  directionLo := (343699234374506619241/100000000000000000000)
  directionHi := (171849617187253309621/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree051.table
  base := (-8045976632463606419821256619601993635871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-230208825154264982879720457741490000000000000)
      constant := (3659187196442939818043097762458562449517044561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree051.table
  base := (-8045980021859154434475067792276704593143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-956119059877205619988466132841010000000000000)
      constant := (15336809703851220484158441519932441266666920617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343699234374506619241/100000000000000000000)
  centralHi := (171849617187253309621/50000000000000000000)
  directionLo := (347119211487659485769/100000000000000000000)
  directionHi := (34711921148765948577/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree052.table
  base := (-3971422716363198691956873526415121926679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-234529173470594703798802748910430000000000000)
      constant := (3802409926570884685504783065525603942959724978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree052.table
  base := (-3971424019656363195537689400704942728793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-974069577823971778980510770259070000000000000)
      constant := (15936994837491481448830791039287734793327185934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (347119211487659485769/100000000000000000000)
  centralHi := (34711921148765948577/10000000000000000000)
  directionLo := (350505820576501858697/100000000000000000000)
  directionHi := (175252910288250929349/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree053.table
  base := (-3913559877489911374698061608129534760247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-238849521786924424717885040079370000000000000)
      constant := (3948408814660970450640008355770687531457079154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree053.table
  base := (-3913560879406691696022691249139720975109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-992020095770737937972555407677130000000000000)
      constant := (16548809608953125292206218243100875696172527542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350505820576501858697/100000000000000000000)
  centralHi := (175252910288250929349/50000000000000000000)
  directionLo := (70772003937206512991/20000000000000000000)
  directionHi := (88465004921508141239/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree054.table
  base := (-1539760002656049699219877922970903453389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-243169870103254145636967331248310000000000000)
      constant := (4097183856320473126768746506400628426314980495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree054.table
  base := (-1539760310639127451112345948960835196957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1009970613717504096964600045095190000000000000)
      constant := (17172254001950367703554948845072388788808606415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70772003937206512991/20000000000000000000)
  centralHi := (88465004921508141239/25000000000000000000)
  directionLo := (357182721875501412193/100000000000000000000)
  directionHi := (178591360937750706097/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree055.table
  base := (-755788653277560835092660561568288286419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-247490218419583866556049622417250000000000000)
      constant := (4248735048099898284982282960590220295693808290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree055.table
  base := (-7557887715772020287017504054933877544431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-8495215964167522776501195723250000000000000)
      constant := (147168000030339040985496756729168870206460409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357182721875501412193/100000000000000000000)
  centralHi := (178591360937750706097/50000000000000000000)
  directionLo := (360474798121289244323/100000000000000000000)
  directionHi := (90118699530322311081/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree056.table
  base := (-7404379571018179931724758749210635010173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-251810566735913587475131913586190000000000000)
      constant := (4403062387266873812032879027628744373177074643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree056.table
  base := (-7404380479521920003584972245641004061301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1045871649611036414948689319931310000000000000)
      constant := (18454031603938321433139092613739835301598311019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360474798121289244323/100000000000000000000)
  centralHi := (90118699530322311081/25000000000000000000)
  directionLo := (72747415996659751147/20000000000000000000)
  directionHi := (45467134997912344467/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree057.table
  base := (-144765586681654601616457188545571418121/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-256130915052243308394214204755130000000000000)
      constant := (4560165871635152506490266236056981641257715550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree057.table
  base := (-3619140015781413062461577697134464230567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-55990640397779082838985997755230000000000000)
      constant := (1005913936556777950357498857574955733467852934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72747415996659751147/20000000000000000000)
  centralHi := (45467134997912344467/12500000000000000000)
  directionLo := (366970362057985708671/100000000000000000000)
  directionHi := (2866955953578013349/781250000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree058.table
  base := (-7059585988760050118103923396320763398303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-260451263368573029313296495924070000000000000)
      constant := (4720045499435250863241805671821013021107403473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree058.table
  base := (-1764896631016953707028094822496419135579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1081772685504568732932778594767430000000000000)
      constant := (19782327568945330689714218893985755662955094804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366970362057985708671/100000000000000000000)
  centralHi := (2866955953578013349/781250000000000000)
  directionLo := (370175404238533327297/100000000000000000000)
  directionHi := (185087702119266663649/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree059.table
  base := (-6868299671785188562913698218055690983177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-264771611684902750232378787093010000000000000)
      constant := (4882701269216546752545758299038567174359475207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree059.table
  base := (-6868300082505767233482950836360814311363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1099723203451334891924823232185490000000000000)
      constant := (20463919921557364135687166278069803270065352797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370175404238533327297/100000000000000000000)
  centralHi := (185087702119266663649/50000000000000000000)
  directionLo := (14934117352015364329/4000000000000000000)
  directionHi := (186676466900192054113/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree060.table
  base := (-166610512420625101352703007485795057077/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-269091960001232471151461078261950000000000000)
      constant := (5048133179773148471102501488368328009578804280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree060.table
  base := (-208263150370763722056736948863518468709/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1117673721398101050916867869603550000000000000)
      constant := (21157141847828911235149934150879164792586309472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14934117352015364329/4000000000000000000)
  centralHi := (186676466900192054113/50000000000000000000)
  directionLo := (188251823664172267531/50000000000000000000)
  directionHi := (376503647328344535063/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree061.table
  base := (-6447948559772400887087923790077441530073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-273412308317562192070543369430890000000000000)
      constant := (5216341230087728197242128851216888422807455543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree061.table
  base := (-3223974400676773819665955516851938892639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1135624239344867209908912507021610000000000000)
      constant := (21861993343863202331341727179544760914461271682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188251823664172267531/50000000000000000000)
  centralHi := (376503647328344535063/100000000000000000000)
  directionLo := (7592564249994566351/2000000000000000000)
  directionHi := (379628212499728317551/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree062.table
  base := (-6218883942760722185594416312734861646493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-277732656633891912989625660599830000000000000)
      constant := (5387325419288933293764868855014575852792355763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree062.table
  base := (-3109442063981162857936063642565374229741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1153574757291633368900957144439670000000000000)
      constant := (22578474406297270742750884005520023776541366758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7592564249994566351/2000000000000000000)
  centralHi := (379628212499728317551/100000000000000000000)
  directionLo := (191363634868234121509/50000000000000000000)
  directionHi := (382727269736468243019/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree063.table
  base := (-149430667930266199940938546941003222621/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-282053004950221633908707951768770000000000000)
      constant := (5561085746619061766041384003756795872448552440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree063.table
  base := (-2988613429576789369510306535294899635947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1171525275238399527893001781857730000000000000)
      constant := (23306585032184273666543435240730086978004398186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191363634868234121509/50000000000000000000)
  centralHi := (382727269736468243019/100000000000000000000)
  directionLo := (385801433737776253099/100000000000000000000)
  directionHi := (3858014337377762531/1000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree064.table
  base := (-5722976946145561339008086679536532823247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-286373353266551354827790242937710000000000000)
      constant := (5737622211409498543657149846703516923278172577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree064.table
  base := (-715372131863335246252069006841818169471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1189475793185165686885046419275790000000000000)
      constant := (24046325218904252011933192103519220324314697992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385801433737776253099/100000000000000000000)
  centralHi := (3858014337377762531/1000000000000000000)
  directionLo := (388851294903741064489/100000000000000000000)
  directionHi := (38885129490374106449/10000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree065.table
  base := (-5456134685953649747047483715130039421867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-290693701582881075746872534106650000000000000)
      constant := (5916934813062021345028511121192685411773412997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree065.table
  base := (-341008423079346419161668690246048961747/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1207426311131931845877091056693850000000000000)
      constant := (24797694964096339140248152217190297364830868688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388851294903741064489/100000000000000000000)
  centralHi := (38885129490374106449/10000000000000000000)
  directionLo := (78375484131840268257/20000000000000000000)
  directionHi := (195938710329600670643/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree066.table
  base := (-2588349993865715083006922137156732828413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-295014049899210796665954825275590000000000000)
      constant := (6099023551034547221893833524549828442846732966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree066.table
  base := (-161771876610627452718639983186873107233/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-10127081232055355412141617306710000000000000)
      constant := (211245407153778121615697053998405241865244384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78375484131840268257/20000000000000000000)
  centralHi := (195938710329600670643/50000000000000000000)
  directionLo := (394880356686301987607/100000000000000000000)
  directionHi := (49360044585787748451/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree067.table
  base := (-2442336449155233457300777707991401871393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-299334398215540517585037116444530000000000000)
      constant := (6283888424830240108396088304467118435092783326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree067.table
  base := (-2442336473584017194138010396579159366713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1243327347025464163861180331529970000000000000)
      constant := (26335323121451402422977013054727971479405218894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394880356686301987607/100000000000000000000)
  centralHi := (49360044585787748451/12500000000000000000)
  directionLo := (39786062807331605013/10000000000000000000)
  directionHi := (397860628073316050131/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree068.table
  base := (-2290026730522093624020586620161403868107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-303654746531870238504119407613470000000000000)
      constant := (6471529433989163494784534491277695332726505674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree068.table
  base := (-4580053498445573094416620735543183234907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1261277864972230322853224968948030000000000000)
      constant := (27121581529781724304481736905203658213116027333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39786062807331605013/10000000000000000000)
  centralHi := (397860628073316050131/100000000000000000000)
  directionLo := (400818740386581680287/100000000000000000000)
  directionHi := (12525585637080677509/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree069.table
  base := (-4262841716412916172245400029307754503703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-307975094848199959423201698782410000000000000)
      constant := (6661946578081861613071444226472094032470214873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree069.table
  base := (-852568349007641724662464800904128391379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1279228382918996481845269606366090000000000000)
      constant := (27919469488865489042197885318021313838680869505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400818740386581680287/100000000000000000000)
  centralHi := (12525585637080677509/3125000000000000000)
  directionLo := (16150207226870045573/4000000000000000000)
  directionHi := (201877590335875569663/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree070.table
  base := (-491629712811382927555398378868038295567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-312295443164529680342283989951350000000000000)
      constant := (6855139856704403050396991566260211853778637576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree070.table
  base := (-1966518862197476893046628322476113677461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1297178900865762640837314243784150000000000000)
      constant := (28728986997066886307522483257415341756909652118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16150207226870045573/4000000000000000000)
  centralHi := (201877590335875569663/50000000000000000000)
  directionLo := (406670418389967043651/100000000000000000000)
  directionHi := (101667604597491760913/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree071.table
  base := (-3590641455309676773518871943012279277927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-316615791480859401261366281120290000000000000)
      constant := (7051109269474534420853774572006302729140472457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree071.table
  base := (-1795320736033492477799900603831425612367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1315129418812528799829358881202210000000000000)
      constant := (29550134052833005165313489973183158995652394146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406670418389967043651/100000000000000000000)
  centralHi := (101667604597491760913/25000000000000000000)
  directionLo := (409564906294061388661/100000000000000000000)
  directionHi := (204782453147030694331/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree072.table
  base := (-161782650456973908569814628604354578627/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-320936139797189122180448572289230000000000000)
      constant := (7249854816028677635381141248420408045506923140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree072.table
  base := (-6319634808509612608494241132330857301/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1333079936759294958821403518620270000000000000)
      constant := (30382910654682945292155419092484031780984329728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409564906294061388661/100000000000000000000)
  centralHi := (204782453147030694331/50000000000000000000)
  directionLo := (412439081249407943089/100000000000000000000)
  directionHi := (41243908124940794309/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree073.table
  base := (-1434036198356690529555271108544140249473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-325256488113518843099530863458170000000000000)
      constant := (7451376496019569215240714290694290432186681886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree073.table
  base := (-717018101628847515942800119474228977899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1351030454706061117813448156038330000000000000)
      constant := (31227316801199230885974469951535804816065575124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412439081249407943089/100000000000000000000)
  centralHi := (41243908124940794309/10000000000000000000)
  directionLo := (415293365003641934413/100000000000000000000)
  directionHi := (207646682501820967207/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree074.table
  base := (-155493728087679049398118125098864316901/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-329576836429848564018613154627110000000000000)
      constant := (7655674309114389135969002671696038375391956656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree074.table
  base := (-2487899656897449877942874891507305533421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1368980972652827276805492793456390000000000000)
      constant := (32083352491020977784116429822539049386994637299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415293365003641934413/100000000000000000000)
  centralHi := (207646682501820967207/50000000000000000000)
  directionLo := (104532041227271736477/25000000000000000000)
  directionHi := (418128164909086945909/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree075.table
  base := (-16761078378872710760504030284646363671/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-333897184746178284937695445796050000000000000)
      constant := (7862748254993263746643867514098773340976795125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree075.table
  base := (-130945925193023913738628132783044439871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1386931490599593435797537430874450000000000000)
      constant := (32951017722838398904429563305000461373151917584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104532041227271736477/25000000000000000000)
  centralHi := (418128164909086945909/100000000000000000000)
  directionLo := (105235968650348182859/25000000000000000000)
  directionHi := (420943874601392731437/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree076.table
  base := (-1689777869626989793436191461087503566889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-338217533062508005856777736964990000000000000)
      constant := (8072598333348055315191565737476242674658874599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree076.table
  base := (-844888937003008732198225708249046621913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-73941158344545241831030635173290000000000000)
      constant := (1780542762915175502669510915827990883632444026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105235968650348182859/25000000000000000000)
  centralHi := (420943874601392731437/100000000000000000000)
  directionLo := (211870437318792477957/50000000000000000000)
  directionHi := (84748174927516991183/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree077.table
  base := (-1271828894238608657757774591372210223219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-342537881378837726775860028133930000000000000)
      constant := (8285224543881371918406852718363712221741869629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree077.table
  base := (-1271828897585020641735875588319515014501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-11758946499943188047782038890170000000000000)
      constant := (286952370309508847664419070138836655079765139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211870437318792477957/50000000000000000000)
  centralHi := (84748174927516991183/20000000000000000000)
  directionLo := (213259766548227475307/50000000000000000000)
  directionHi := (85303906619290990123/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree078.table
  base := (-5258049364314924671896841990933195917/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-346858229695167447694942319302870000000000000)
      constant := (8500626886305747397706700314740890355922647520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree078.table
  base := (-420643950423627610061939505245255843757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1440783044439891912773671343128630000000000000)
      constant := (35623790657844764953765694813382983958977700966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213259766548227475307/50000000000000000000)
  centralHi := (85303906619290990123/20000000000000000000)
  directionLo := (85856041228794231109/20000000000000000000)
  directionHi := (214640103071985577773/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree079.table
  base := (-199077454004018555794371363113708917611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-351178578011497168614024610471810000000000000)
      constant := (8718805360342953201547565144723573324186129802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree079.table
  base := (-199077454980661670557177516173670250989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1458733562386658071765715980546690000000000000)
      constant := (36537974045427846999688453765090715819533098982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85856041228794231109/20000000000000000000)
  centralHi := (214640103071985577773/50000000000000000000)
  directionLo := (432023238566171126853/100000000000000000000)
  directionHi := (216011619283085563427/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree080.table
  base := (11514010239659494480213386245253510491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-355498926327826889533106901640750000000000000)
      constant := (8939759965723413087009643546365379472463995095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree080.table
  base := (11514009941269462780723435987721274711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1476684080333424230757760617964750000000000000)
      constant := (37463786969091785777612227974864898265003255955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432023238566171126853/100000000000000000000)
  centralHi := (216011619283085563427/50000000000000000000)
  directionLo := (6792952566746738769/1562500000000000000)
  directionHi := (434748964271791281217/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree081.table
  base := (262943477343237248556483033357148354913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-359819274644156610452189192809690000000000000)
      constant := (9163490702185698576963227880169391973794544034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree081.table
  base := (525886953547077178389214210446478991921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1494634598280190389749805255382810000000000000)
      constant := (38401229427761649555390947735074692648846101201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/1562500000000000000)
  centralHi := (434748964271791281217/100000000000000000000)
  directionLo := (8749154135334173951/2000000000000000000)
  directionHi := (437457706766708697551/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree082.table
  base := (100679577854082221593101636666250987263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-364139622960486331371271483978630000000000000)
      constant := (9389997569476088309848469656566902567238731670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree082.table
  base := (125849472208850038583739140962153400949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1512585116226956548741849892800870000000000000)
      constant := (39350301420393896362539053571550162581654826152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8749154135334173951/2000000000000000000)
  centralHi := (437457706766708697551/100000000000000000000)
  directionLo := (88029955920420665229/20000000000000000000)
  directionHi := (220074889801051663073/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree083.table
  base := (1500296499535409999784684851568514242057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-368459971276816052290353775147570000000000000)
      constant := (9619280567348178387621559591178370367593982713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree083.table
  base := (150029649887117630036053721172441492131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1530535634173722707733894530218930000000000000)
      constant := (40311002945974850043852596579986454168177742110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88029955920420665229/20000000000000000000)
  centralHi := (220074889801051663073/50000000000000000000)
  directionLo := (221412743399049060859/50000000000000000000)
  directionHi := (442825486798098121719/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree084.table
  base := (626996592219123430647727497953488367/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-372780319593145773209436066316510000000000000)
      constant := (9851339695562533834468289091415443385873609600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree084.table
  base := (501597273648536797765322163412359362009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1548486152120488866725939167636990000000000000)
      constant := (41283334003519326793475991192293941077167660516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221412743399049060859/50000000000000000000)
  centralHi := (442825486798098121719/100000000000000000000)
  directionLo := (22274256162224868701/5000000000000000000)
  directionHi := (445485123244497374021/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree085.table
  base := (315634192912040839331013623748591978277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-377100667909475494128518357485450000000000000)
      constant := (10086174953886373559111574243842290498380325544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree085.table
  base := (2525073542909322549588509901259191060247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1566436670067255025717983805055050000000000000)
      constant := (42267294592069385226984704062934402724702649207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22274256162224868701/5000000000000000000)
  centralHi := (445485123244497374021/100000000000000000000)
  directionLo := (448128975080118486179/100000000000000000000)
  directionHi := (22406448754005924309/5000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree086.table
  base := (764087455694764000604640847473581620173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-381421016225805215047600648654390000000000000)
      constant := (10323786342093282944213373214895208909633661428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree086.table
  base := (6112699644967431573460752691681468487/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1584387188014021184710028442473110000000000000)
      constant := (43262884710693179157175373481174649112490323500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448128975080118486179/100000000000000000000)
  centralHi := (22406448754005924309/5000000000000000000)
  directionLo := (450757320052098428299/100000000000000000000)
  directionHi := (4507573200520984283/1000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree087.table
  base := (3600217912782817816310395620951022841479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-385741364542134935966682939823330000000000000)
      constant := (10564173859962949501422679168248549401325250711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree087.table
  base := (720043582511492155488033031220488352793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1602337705960787343702073079891170000000000000)
      constant := (44270104358483896871839833547021030758691755165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450757320052098428299/100000000000000000000)
  centralHi := (4507573200520984283/1000000000000000000)
  directionLo := (90674085571290397543/20000000000000000000)
  directionHi := (113342606964112996929/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree088.table
  base := (1039169448273288195606460496887424033909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-390061712858464656885765230992270000000000000)
      constant := (10807337507280918031241810728855594726302962324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree088.table
  base := (4156677792921218452377413228420231243921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-13390811767831020683422460473630000000000000)
      constant := (374288872186436150670167136294579703479055481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90674085571290397543/20000000000000000000)
  centralHi := (113342606964112996929/25000000000000000000)
  directionLo := (455968560461063781373/100000000000000000000)
  directionHi := (227984280230531890687/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree089.table
  base := (2362864722013101704301897244566865561807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-394382061174794377804847522161210000000000000)
      constant := (11053277283838362489536430701938439753490420926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree089.table
  base := (236286472194752217299166731401423511779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1638238741854319661686162354727290000000000000)
      constant := (46319432238058171580726469986627491608360369980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455968560461063781373/100000000000000000000)
  centralHi := (227984280230531890687/50000000000000000000)
  directionLo := (57318996551526115999/12500000000000000000)
  directionHi := (458551972412208927993/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree090.table
  base := (1061474569281715245003133174598724378691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-398702409491124098723929813330150000000000000)
      constant := (11301993189431872344985127605333089334667664095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree090.table
  base := (2653686423154267443560093451906852521357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1656189259801085820678206992145350000000000000)
      constant := (47361540468144706522357705303963986449970790234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57318996551526115999/12500000000000000000)
  centralHi := (458551972412208927993/100000000000000000000)
  directionLo := (230560455562808763739/50000000000000000000)
  directionHi := (461120911125617527479/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree091.table
  base := (1475401995389600754900536391271306591009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-403022757807453819643012104499090000000000000)
      constant := (11553485223863251657726164213159509166496057924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree091.table
  base := (236064319259284241405882573570144963259/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1674139777747851979670251629563410000000000000)
      constant := (48415278224002436145504694041050217553502909475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230560455562808763739/50000000000000000000)
  centralHi := (461120911125617527479/100000000000000000000)
  directionLo := (3622465759086132603/781250000000000000)
  directionHi := (92735123432604994637/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree092.table
  base := (6508434831267466634069581965543865003113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-407343106123783540562094395668030000000000000)
      constant := (11807753386939329451927203175594734863818025817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree092.table
  base := (1627108707802321343497586009395511674829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1692090295694618138662296266981470000000000000)
      constant := (49480645504836083528560924276132541381872822196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3622465759086132603/781250000000000000)
  centralHi := (92735123432604994637/20000000000000000000)
  directionLo := (1165540811237707529/250000000000000000)
  directionHi := (466216324495083011601/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree093.table
  base := (3563926688892140832388527478687799934477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-411663454440113261481176686836970000000000000)
      constant := (12064797678471780218941017971117577739009732986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree093.table
  base := (7127853377739919996113712716322066203171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1710040813641384297654340904399530000000000000)
      constant := (50557642309870304242372302308719084173820712451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1165540811237707529/250000000000000000)
  centralHi := (466216324495083011601/100000000000000000000)
  directionLo := (468743260751444809911/100000000000000000000)
  directionHi := (58592907593930601239/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree094.table
  base := (1551972720759607933728863517137981074739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-415983802756442982400258978005910000000000000)
      constant := (12324618098276953591994970259783604206109530255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree094.table
  base := (3879931801882109479202402461047968360387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1727991331588150456646385541817590000000000000)
      constant := (51646268638348989308752736903440852611900129094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468743260751444809911/100000000000000000000)
  centralHi := (58592907593930601239/12500000000000000000)
  directionLo := (117814161864695149281/25000000000000000000)
  directionHi := (3770053179670244777/800000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree095.table
  base := (8404465492423343453410445916202937824713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-420304151072772703319341269174850000000000000)
      constant := (12587214646175712392276363899573996967382380217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree095.table
  base := (336178619695902476821794363485716342903/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-91891676291311400823075272591350000000000000)
      constant := (2776132867870242190874566538750341546808349925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117814161864695149281/25000000000000000000)
  centralHi := (3770053179670244777/800000000000000000)
  directionLo := (473756700267428261813/100000000000000000000)
  directionHi := (236878350133714130907/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree096.table
  base := (362466361087426670119272095972773610631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-424624499389102424238423560343790000000000000)
      constant := (12852587321993278370628211489725098880879606975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree096.table
  base := (4530829513583007824857364786477545254807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1763892367481682774630474816653710000000000000)
      constant := (53858409862707543318421611206530331308550449134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473756700267428261813/100000000000000000000)
  centralHi := (236878350133714130907/50000000000000000000)
  directionLo := (476243629167335216257/100000000000000000000)
  directionHi := (238121814583667608129/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree097.table
  base := (7785155353605987858887886222149003597/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-428944847705432145157505851512730000000000000)
      constant := (13120736125559085067044084883345653473950716250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree097.table
  base := (9731444191992508047789403385412663520703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1781842885428448933622519454071770000000000000)
      constant := (54981924757165551797849079121666230555247827743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476243629167335216257/100000000000000000000)
  centralHi := (238121814583667608129/50000000000000000000)
  directionLo := (119679409673475877469/25000000000000000000)
  directionHi := (478717638693903509877/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree098.table
  base := (650863810699689301850544508068006265721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-433265196021761866076588142681670000000000000)
      constant := (13391661056706637287946192368160875655568545424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree098.table
  base := (10413820971183615722958809023388291403303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1799793403375215092614564091489830000000000000)
      constant := (56117069172223122637721512248423443956787678343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119679409673475877469/25000000000000000000)
  centralHi := (478717638693903509877/100000000000000000000)
  directionLo := (481178928124309266937/100000000000000000000)
  directionHi := (240589464062154633469/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree099.table
  base := (2777197337356405690317350674471467038121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-437585544338091586995670433850610000000000000)
      constant := (13665362115273376763547531558296191175229702756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree099.table
  base := (2777197337354231565251407221494113749499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-15022677035718853319062882057090000000000000)
      constant := (473254901712487252408045321790717500254276556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481178928124309266937/100000000000000000000)
  centralHi := (240589464062154633469/50000000000000000000)
  directionLo := (483627691664829738661/100000000000000000000)
  directionHi := (241813845832414869331/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree100.table
  base := (11816349311735566378670737417856751864671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-441905892654421307914752725019550000000000000)
      constant := (13941839301100553598002778527121042280532294639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree100.table
  base := (472653972469157621418394476004803869849/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1835694439268747410598653366325950000000000000)
      constant := (58422246561475435903461658069554145945971854225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483627691664829738661/100000000000000000000)
  centralHi := (241813845832414869331/50000000000000000000)
  directionLo := (486064118629676330611/100000000000000000000)
  directionHi := (121516029657419082653/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree101.table
  base := (12536500843508531558505234493823752031751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-446226240970751028833835016188490000000000000)
      constant := (14221092614033103166251764200270396185304846359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree101.table
  base := (6268250421751741922610476355980106019181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1853644957215513569590698003744010000000000000)
      constant := (59592279534378108596867261288643514022047690522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486064118629676330611/100000000000000000000)
  centralHi := (121516029657419082653/25000000000000000000)
  directionLo := (244244196805899825239/50000000000000000000)
  directionHi := (488488393611799650479/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree102.table
  base := (6634621965232221315481229108082056574381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-450546589287080749752917307357430000000000000)
      constant := (14503122053919528145513469665300865076395216058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree102.table
  base := (3317310982615149386498357978713213149751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1871595475162279728582742641162070000000000000)
      constant := (60773942025295212748048823194793307454377093724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244244196805899825239/50000000000000000000)
  centralHi := (488488393611799650479/100000000000000000000)
  directionLo := (490900696646102699563/100000000000000000000)
  directionHi := (122725174161525674891/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree103.table
  base := (14014578558648813977969871619888342947193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (2079)
      previous := (0)
      next := (1320)
      square := (34288478701029531103827707690000000000000)
      linear := (-4416183860227286123029122315790000000000000)
      constant := (143572112821473644639473430850008499323560879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree103.table
  base := (2802915711729177054398000759942756255597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1889545993109045887574787278580130000000000000)
      constant := (61967234033617206369352388924135017680003662785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490900696646102699563/100000000000000000000)
  centralHi := (122725174161525674891/25000000000000000000)
  directionLo := (493301203365470604517/100000000000000000000)
  directionHi := (246650601682735302259/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree104.table
  base := (14772504714422520435496322307568251749007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-459187285919740191591081889695310000000000000)
      constant := (15075509313965177444443438841236111582805215263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree104.table
  base := (14772504714420289921344152704495686726711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1907496511055812046566831915998190000000000000)
      constant := (63172155558748321807511327206034756091909463191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493301203365470604517/100000000000000000000)
  centralHi := (246650601682735302259/50000000000000000000)
  directionLo := (495690085149999573321/100000000000000000000)
  directionHi := (247845042574999786661/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree105.table
  base := (7771511192225988993701891237811094478733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-463507634236069912510164180864250000000000000)
      constant := (15365867133838248292419287719388375802649756794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree105.table
  base := (3885755596112569843690227389984360737541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1925447029002578205558876553416250000000000000)
      constant := (64388706600106137046022714496578127445506113684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495690085149999573321/100000000000000000000)
  centralHi := (247845042574999786661/50000000000000000000)
  directionLo := (124516877317445974251/25000000000000000000)
  directionHi := (99613501853956779401/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree106.table
  base := (16326131555699713922628509125518368758833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-467827982552399633429246472033190000000000000)
      constant := (15659001080092683393801634762536244374162459297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree106.table
  base := (16326131555698420487527430474728961252449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1943397546949344364550921190834310000000000000)
      constant := (65616887157121163967692349061748815756468224769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124516877317445974251/25000000000000000000)
  centralHi := (99613501853956779401/20000000000000000000)
  directionLo := (500433639021597656647/100000000000000000000)
  directionHi := (62554204877699707081/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree107.table
  base := (2140229026926913387765179845331611002167/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-472148330868729354348328763202130000000000000)
      constant := (15954911152593213530726308456065464488975917624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree107.table
  base := (17121832215414322282724254544748166111209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1961348064896110523542965828252370000000000000)
      constant := (66856697229236452744257411929793864643903720329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500433639021597656647/100000000000000000000)
  centralHi := (62554204877699707081/12500000000000000000)
  directionLo := (20111545354391487913/4000000000000000000)
  directionHi := (251394316929893598913/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree108.table
  base := (17930124351126680286240683315607700723311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-476468679185059075267411054371070000000000000)
      constant := (16253597351207522435757948009426362096973606399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree108.table
  base := (17930124351125930511292611408609771222997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1979298582842876682535010465670430000000000000)
      constant := (68108136815907211574064766952557603416791731957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20111545354391487913/4000000000000000000)
  centralHi := (251394316929893598913/50000000000000000000)
  directionLo := (505132649521671277723/100000000000000000000)
  directionHi := (126283162380417819431/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree109.table
  base := (4687751987657931909398704296262709322683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-480789027501388796186493345540010000000000000)
      constant := (16555059675806157968067667788435624332817375788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree109.table
  base := (18751007950631156858134823527229526621631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-1997249100789642841527055103088490000000000000)
      constant := (69371205916600441037422632477455292952359463711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505132649521671277723/100000000000000000000)
  centralHi := (126283162380417819431/25000000000000000000)
  directionLo := (507465838147727960701/100000000000000000000)
  directionHi := (253732919073863980351/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree110.table
  base := (4896120750497565390603046631469045974991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-485109375817718517105575636708950000000000000)
      constant := (16859298126262446677473144317450520434994718076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree110.table
  base := (3916896600397965416539114083720560853627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-16654542303606685954703303640550000000000000)
      constant := (583850450667723821349829021078615612340796735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507465838147727960701/100000000000000000000)
  centralHi := (253732919073863980351/50000000000000000000)
  directionLo := (509788348396830732643/100000000000000000000)
  directionHi := (127447087099207683161/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree111.table
  base := (20430549493516264003939734086897567889093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-489429724134048238024657927877890000000000000)
      constant := (17166312702452411598410284412093216297735387637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree111.table
  base := (20430549493515933303252178396538088524973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2033150136683175159511144377924610000000000000)
      constant := (71932232657979179101503276062442660244859345613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509788348396830732643/100000000000000000000)
  centralHi := (127447087099207683161/25000000000000000000)
  directionLo := (64012540694597603599/12500000000000000000)
  directionHi := (512100325556780828793/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree112.table
  base := (21289207413770428168848798529126184010451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-493750072450377958943740219046830000000000000)
      constant := (17476103404254693125108664304218379686166874659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree112.table
  base := (21289207413770176478968591198682119009331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2051100654629941318503189015342670000000000000)
      constant := (73230190297654551170541766239649953640446587411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64012540694597603599/12500000000000000000)
  centralHi := (512100325556780828793/100000000000000000000)
  directionLo := (257200955825184168733/50000000000000000000)
  directionHi := (514401911650368337467/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree113.table
  base := (1108022837577648873190277271164343214081/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-498070420766707679862822510215770000000000000)
      constant := (17788670231550472827689605344365830343163706580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree113.table
  base := (2770057093944098240331325464988928756251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2069051172576707477495233652760730000000000000)
      constant := (74539777449331481407057452008937471176014399448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200955825184168733/50000000000000000000)
  centralHi := (514401911650368337467/100000000000000000000)
  directionLo := (516693245537181174177/100000000000000000000)
  directionHi := (258346622768590587089/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree114.table
  base := (180033574186693352762725538043268922839/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-502390769083037400781904801384710000000000000)
      constant := (18104013184223400076695571180044153120307065728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree114.table
  base := (11522148747948301699098081100395565061853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-109842194238077559815119910009410000000000000)
      constant := (3992683900659521756428376818949438808154400094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516693245537181174177/100000000000000000000)
  centralHi := (258346622768590587089/50000000000000000000)
  directionLo := (259487231505684222373/50000000000000000000)
  directionHi := (518974463011368444747/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree115.table
  base := (23940729636060530932384796362105349480353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-506711117399367121700987092553650000000000000)
      constant := (18422132262159521350772908296939575652637064977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree115.table
  base := (23940729636060420026575295209396149765951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2104952208470239795479322927596850000000000000)
      constant := (77193840286783660320741980710837633217926505631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259487231505684222373/50000000000000000000)
  centralHi := (518974463011368444747/100000000000000000000)
  directionLo := (260622848447776482869/50000000000000000000)
  directionHi := (521245696895552965739/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree116.table
  base := (12424876580761319615283438067794205219457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-511031465715696842620069383722590000000000000)
      constant := (18743027465247212108932722748272977446346438626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree116.table
  base := (776554786297579839008602717005373460217/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2122902726417005954471367565014910000000000000)
      constant := (78538315971630124706873440522404654979703640864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260622848447776482869/50000000000000000000)
  centralHi := (521245696895552965739/100000000000000000000)
  directionLo := (261753538565538362481/50000000000000000000)
  directionHi := (523507077131076724963/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree117.table
  base := (6442842015493682167577525711380973283983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-515351814032026563539151674891530000000000000)
      constant := (19066698793377111115061244692344942982279102588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree117.table
  base := (5154273612394932894613552353342268800231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2140853244363772113463412202432970000000000000)
      constant := (79894421166620027782904973318479138217314451555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261753538565538362481/50000000000000000000)
  centralHi := (523507077131076724963/100000000000000000000)
  directionLo := (262879365432376394023/50000000000000000000)
  directionHi := (525758730864752788047/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree118.table
  base := (2670557432731582263067683900131753422263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-519672162348356284458233966060470000000000000)
      constant := (19393146246442057108186946733017757720567881670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree118.table
  base := (834549197728617931048746742937419153433/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2158803762310538272455456839851030000000000000)
      constant := (81262155871312148855170553158153400993315419936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262879365432376394023/50000000000000000000)
  centralHi := (525758730864752788047/100000000000000000000)
  directionLo := (264000391266143768859/50000000000000000000)
  directionHi := (528000782532287537719/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree119.table
  base := (27652371947646555400051860383555679849309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-523992510664686005377316257229410000000000000)
      constant := (19722369824337027717475302956547662207521319181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree119.table
  base := (27652371947646518250567875329475060249449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2176754280257304431447501477269090000000000000)
      constant := (82641520085274073780360471877969080106756181769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264000391266143768859/50000000000000000000)
  centralHi := (528000782532287537719/100000000000000000000)
  directionLo := (530233353938528123277/100000000000000000000)
  directionHi := (265116676969264061639/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree120.table
  base := (28611760913263616875699851080952816125809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-528312858981015726296398548398350000000000000)
      constant := (20054369526959080526046394396431828426278707681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree120.table
  base := (7152940228315897154688839968030871891207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2194704798204070590439546114687150000000000000)
      constant := (84032513808081952308202812785880226060319251868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530233353938528123277/100000000000000000000)
  centralHi := (265116676969264061639/50000000000000000000)
  directionLo := (16639267635458798599/3125000000000000000)
  directionHi := (532456564334681555169/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree121.table
  base := (29583741214654391224231869808588913850101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-532633207297345447215480839567290000000000000)
      constant := (20389145354207296192523797774578539787035721509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree121.table
  base := (29583741214654369732680549565492645734841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-18286407571494518590343725224010000000000000)
      constant := (706075512721655073517817459696122845110277601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16639267635458798599/3125000000000000000)
  centralHi := (532456564334681555169/100000000000000000000)
  directionLo := (534670530492643963673/100000000000000000000)
  directionHi := (267335265246321981837/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree122.table
  base := (30568312842491781343444821342237024391373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-536953555613675168134563130736230000000000000)
      constant := (20726697305982723543750240453753972591768076157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree122.table
  base := (15284156421245882499296601302044006426183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2230605834097602908423635389523270000000000000)
      constant := (86849389778581591636408167077715188489404199246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534670530492643963673/100000000000000000000)
  centralHi := (267335265246321981837/50000000000000000000)
  directionLo := (536875366776571114463/100000000000000000000)
  directionHi := (16777355211767847327/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree123.table
  base := (25252380630103369094227037924256480621/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-541273903930004889053645421905170000000000000)
      constant := (21067025382188326556368050412051926253635236250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree123.table
  base := (15782737893814599468974820824057124610849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2248556352044369067415680026941330000000000000)
      constant := (88275272025466403966981309779453598520252990338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536875366776571114463/100000000000000000000)
  centralHi := (16777355211767847327/3125000000000000000)
  directionLo := (134767796302953575791/25000000000000000000)
  directionHi := (107814237042362860633/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree124.table
  base := (16287615020547899919182428728974525802067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-545594252246334609972727713074110000000000000)
      constant := (21410129582728933148979927924284701488468257606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree124.table
  base := (16287615020547895193208761362500297701621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2266506869991135226407724664359390000000000000)
      constant := (89712783779582843827236139611380231007809013802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134767796302953575791/25000000000000000000)
  centralHi := (107814237042362860633/20000000000000000000)
  directionLo := (270629047775669602319/50000000000000000000)
  directionHi := (541258095551339204639/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree125.table
  base := (33597575594091696515708790776169170481761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-549914600562664330891810004243050000000000000)
      constant := (21756009907511185710395238043881878729641002449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree125.table
  base := (33597575594091689328681062131069598512643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2284457387937901385399769301777450000000000000)
      constant := (91161925040546524968653647825534751132630758883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270629047775669602319/50000000000000000000)
  centralHi := (541258095551339204639/100000000000000000000)
  directionLo := (6792952566746738769/1250000000000000000)
  directionHi := (543436205339739101521/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree126.table
  base := (6926502487596715230112720142346427741123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-554234948878994051810892295411990000000000000)
      constant := (22104666356443493293044666338402186259527869535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree126.table
  base := (17316256218991785343035349392676359413159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2302407905884667544391813939195510000000000000)
      constant := (92622695807980335118472469324339372111052396558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/1250000000000000000)
  centralHi := (543436205339739101521/100000000000000000000)
  directionLo := (545605619974948133603/100000000000000000000)
  directionHi := (136401404993737033401/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree127.table
  base := (8920010141075070711686434508288739850793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-558555297195323772729974586580930000000000000)
      constant := (22456098929435985404025601534048820964308251748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree127.table
  base := (7136008112860055738440334383327286360731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2320358423831433703383858576613570000000000000)
      constant := (94095096081514245721661151372546715977615454055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545605619974948133603/100000000000000000000)
  centralHi := (136401404993737033401/25000000000000000000)
  directionLo := (13694161069193869261/2500000000000000000)
  directionHi := (547766442767754770441/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree128.table
  base := (18370079982364309475527342038043536503289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-562875645511653493649056877749870000000000000)
      constant := (22810307626400467329435239328311687757526786002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree128.table
  base := (36740159964728615792631925977692812495673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2338308941778199862375903214031630000000000000)
      constant := (95579125860785127995844110541798319742623492313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13694161069193869261/2500000000000000000)
  centralHi := (547766442767754770441/100000000000000000000)
  directionLo := (274959387499605295393/50000000000000000000)
  directionHi := (549918774999210590787/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree129.table
  base := (4726608828888659086262380871360290751019/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-567195993827983214568139168918810000000000000)
      constant := (23167292447250376930669670444845710596620484568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree129.table
  base := (4726608828888658786138212334465202482691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2356259459724966021367947851449690000000000000)
      constant := (97074785145436575046729836879382376077171404568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274959387499605295393/50000000000000000000)
  centralHi := (549918774999210590787/100000000000000000000)
  directionLo := (27603135798801231659/5000000000000000000)
  directionHi := (552062715976024633181/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree130.table
  base := (19449086277716439521679120699904692858899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-571516342144312935487221460087750000000000000)
      constant := (23527053391900742854226191994015077773080118982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree130.table
  base := (38898172555432877218261587621804649783761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2374209977671732180359992488867750000000000000)
      constant := (98582073935118729803353740967548548907204464241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27603135798801231659/5000000000000000000)
  centralHi := (552062715976024633181/100000000000000000000)
  directionLo := (554198363084029042319/100000000000000000000)
  directionHi := (6927479538550363029/1250000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree131.table
  base := (312469263514345379663529709576603534263/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-575836690460642656406303751256690000000000000)
      constant := (23889590460268144099252733947546087922559509376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree131.table
  base := (4999508216229525901209960772374483459351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2392160495618498339352037126285810000000000000)
      constant := (100100992229488118543586510864488398495903288248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554198363084029042319/100000000000000000000)
  centralHi := (6927479538550363029/1250000000000000000)
  directionLo := (556325811839797457597/100000000000000000000)
  directionHi := (278162905919898728799/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree132.table
  base := (41106550146598479364067855216302540817889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-580157038776972377325386042425630000000000000)
      constant := (24254903652270670889651845652609233655536984401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree132.table
  base := (20553275073299239154840564912479209528129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-19918272839382351225984146807470000000000000)
      constant := (839930082877747849511648761066129989279309138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556325811839797457597/100000000000000000000)
  centralHi := (278162905919898728799/50000000000000000000)
  directionLo := (11168903118809871129/2000000000000000000)
  directionHi := (558445155940493556451/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree133.table
  base := (42229625798137786787534313214415029064901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-584477387093302098244468333594570000000000000)
      constant := (24622992967827886799975851915653309043349534709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree133.table
  base := (8445925159627557197237744681869244109529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-127792712184843718807164547427470000000000000)
      constant := (5430195648997139914392476035775066961039035855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11168903118809871129/2000000000000000000)
  centralHi := (558445155940493556451/100000000000000000000)
  directionLo := (140139121828005840037/25000000000000000000)
  directionHi := (560556487312023360149/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree134.table
  base := (43365292677007647355945041184331758866313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-588797735409631819163550624763510000000000000)
      constant := (24993858406860792086652457223717995629812714617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree134.table
  base := (43365292677007646746947506947009984399043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2446012049458796816328171038539990000000000000)
      constant := (104727524137377354445803955729550723128534597283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140139121828005840037/25000000000000000000)
  centralHi := (560556487312023360149/100000000000000000000)
  directionLo := (562659896155561318853/100000000000000000000)
  directionHi := (281329948077780659427/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree135.table
  base := (22256775387946825735991737221067225930971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-593118083725961540082632915932450000000000000)
      constant := (25367499969291788178263730142071604399803342678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree135.table
  base := (22256775387946825504594937509535652107981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2463962567405562975320215675958050000000000000)
      constant := (106292960447183077282965361466173053639457436122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562659896155561318853/100000000000000000000)
  centralHi := (281329948077780659427/50000000000000000000)
  directionLo := (282377735496258401297/50000000000000000000)
  directionHi := (112951094198503360519/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree136.table
  base := (45674400087610221405735369722814533965533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-597438432042291261001715207101390000000000000)
      constant := (25743917655044643280673010463915659390840339597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree136.table
  base := (713662501368909703969767407701816844171/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2481913085352329134312260313376110000000000000)
      constant := (107870026260048953664604143871775155940494940864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282377735496258401297/50000000000000000000)
  centralHi := (112951094198503360519/20000000000000000000)
  directionLo := (141710824677001105647/25000000000000000000)
  directionHi := (566843298708004422589/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree137.table
  base := (46847840605097470351651255691912794403187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-601758780358620981920797498270330000000000000)
      constant := (26123111464044459054760223847862882835823410883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree137.table
  base := (46847840605097470084436299005457864419961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2499863603299095293304304950794170000000000000)
      constant := (109458721575666600675534564918308224975728316441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141710824677001105647/25000000000000000000)
  centralHi := (566843298708004422589/100000000000000000000)
  directionLo := (71115433074109822683/12500000000000000000)
  directionHi := (113784692918575716293/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree138.table
  base := (9606774464283631756718106419147888745333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-606079128674950702839879789439270000000000000)
      constant := (26505081396217638326392544665821879758496188985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree138.table
  base := (9606774464283631716111840086327882263473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2517814121245861452296349588212230000000000000)
      constant := (111059046393732992756294676924624461125753820565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71115433074109822683/12500000000000000000)
  centralHi := (113784692918575716293/20000000000000000000)
  directionLo := (570996052384389790359/100000000000000000000)
  directionHi := (14274901309609744759/2500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree139.table
  base := (12308123807438686117368101507148211755743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-610399476991280423758962080608210000000000000)
      constant := (26889827451491853790029827785856061514066709948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree139.table
  base := (49232495229754744315216119739984725723507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2535764639192627611288394225630290000000000000)
      constant := (112671000713950332844857383596802352804328509267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570996052384389790359/100000000000000000000)
  centralHi := (14274901309609744759/2500000000000000000)
  directionLo := (57306114430551758553/10000000000000000000)
  directionHi := (573061144305517585531/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree140.table
  base := (25221854661703261332893491153389163819879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-614719825307610144678044371777150000000000000)
      constant := (27277349629796017669048176729961611277930192622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree140.table
  base := (50443709323406522548594294422145294276563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2553715157139393770280438863048350000000000000)
      constant := (114294584536025927457482923655714728599294548403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57306114430551758553/10000000000000000000)
  centralHi := (573061144305517585531/100000000000000000000)
  directionLo := (575118821103032317459/100000000000000000000)
  directionHi := (28755941055151615873/5000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree141.table
  base := (403652457779584790336392759170046972117/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-619040173623939865597126662946090000000000000)
      constant := (27667647931060252297465260744029503625880224384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree141.table
  base := (51667514595786853074028285347555975295111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2571665675086159929272483500466410000000000000)
      constant := (115929797859672065563303944054699372556865743591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575118821103032317459/100000000000000000000)
  centralHi := (28755941055151615873/5000000000000000000)
  directionLo := (288584581042167831351/50000000000000000000)
  directionHi := (577169162084335662703/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree142.table
  base := (52903911040420470996748990608640979689701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-623360521940269586516208954115030000000000000)
      constant := (28060722355215861589272303739445852153528037909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree142.table
  base := (26451955520210235464558623728968272151389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2589616193032926088264528137884470000000000000)
      constant := (117576640684605901113497813480765546191689645818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288584581042167831351/50000000000000000000)
  centralHi := (577169162084335662703/100000000000000000000)
  directionLo := (289606122576563707303/50000000000000000000)
  directionHi := (579212245153127414607/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree143.table
  base := (27076449325470438887228176710163609184193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-627680870256599307435291245283970000000000000)
      constant := (28456572902195303363024304610554531459670207074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree143.table
  base := (13538224662735219430770581204018512775971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-21550138107270183861624568390930000000000000)
      constant := (985414157111978009023610915105122732448502124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289606122576563707303/50000000000000000000)
  centralHi := (579212245153127414607/100000000000000000000)
  directionLo := (145312036710985983973/25000000000000000000)
  directionHi := (581248146843943935893/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree144.table
  base := (27707238710543905349981676096563437626289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-632001218572929028354373536452910000000000000)
      constant := (28855199571932162490716197104464403019554600002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree144.table
  base := (55414477421087810660940793698524458279779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2625517228926458406248617412720590000000000000)
      constant := (120905214837228924959233625440598526862119026499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145312036710985983973/25000000000000000000)
  centralHi := (581248146843943935893/100000000000000000000)
  directionLo := (291638471177805798367/50000000000000000000)
  directionHi := (116655388471122319347/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree145.table
  base := (11337729468940957299627499669998843609407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-636321566889258749273455827621850000000000000)
      constant := (29256602364361124841282100649861588659260994315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree145.table
  base := (56688647344704786468498247228126218350223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2643467746873224565240662050138650000000000000)
      constant := (122586946164375737369727841732600281343756090863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291638471177805798367/50000000000000000000)
  centralHi := (116655388471122319347/20000000000000000000)
  directionLo := (585298705583656569683/100000000000000000000)
  directionHi := (146324676395914142421/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree146.table
  base := (57975408415736717562152979125769643564081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-640641915205588470192538118790790000000000000)
      constant := (29660781279417951990301200199120510148571335329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree146.table
  base := (14493852103934179384910448373196676188291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2661418264819990724232706687556710000000000000)
      constant := (124280306991725284041616952372112996050322956684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585298705583656569683/100000000000000000000)
  centralHi := (146324676395914142421/25000000000000000000)
  directionLo := (293656754575855250661/50000000000000000000)
  directionHi := (587313509151710501323/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree147.table
  base := (14818690157056899439093104598573210749181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-644962263521918191111620409959730000000000000)
      constant := (30067736317039456668680518828918732771352244916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree147.table
  base := (2963738031411379886963791509902792423919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2679368782766756883224751324974770000000000000)
      constant := (125985297319017400670913846355312797517384116780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293656754575855250661/50000000000000000000)
  centralHi := (587313509151710501323/100000000000000000000)
  directionLo := (58932142444194982401/10000000000000000000)
  directionHi := (589321424441949824011/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree148.table
  base := (60586703976318255414760119687041033976677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-649282611838247912030702701128670000000000000)
      constant := (30477467477163478924215083835421698329458566293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree148.table
  base := (60586703976318255401776351655547823248669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2697319300713523042216795962392830000000000000)
      constant := (127701917145996152780092401489725304467325110589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58932142444194982401/10000000000000000000)
  centralHi := (589321424441949824011/100000000000000000000)
  directionLo := (591322521624604804033/100000000000000000000)
  directionHi := (295661260812302402017/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree149.table
  base := (15477809613561042794049091984344527851823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-653602960154577632949784992297610000000000000)
      constant := (30889974759728862971002776161487464383919960828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree149.table
  base := (30955619227122085583168233742939140538249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2715269818660289201208840599810890000000000000)
      constant := (129430166472409740398953211996688629195702509138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591322521624604804033/100000000000000000000)
  centralHi := (295661260812302402017/50000000000000000000)
  directionLo := (593316869686572839771/100000000000000000000)
  directionHi := (148329217421643209943/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree150.table
  base := (988255688380208724918536022934118363179/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-657923308470907353868867283466550000000000000)
      constant := (31305258164675434702717297262015215949757824704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree150.table
  base := (3162418202816667919364950420965092614643/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2733220336607055360200885237228950000000000000)
      constant := (131170045298010405478827327065331024210004417660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593316869686572839771/100000000000000000000)
  centralHi := (148329217421643209943/25000000000000000000)
  directionLo := (297652268229584510161/50000000000000000000)
  directionHi := (595304536459169020323/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree151.table
  base := (12919616155400860791091899334770326711099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-662243656787237074787949574635490000000000000)
      constant := (31723317691943979846720864885677811980390246455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree151.table
  base := (32299040388502151974887064160770816125949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2751170854553821519192929874647010000000000000)
      constant := (132921553622554341945343243326661140038395156538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297652268229584510161/50000000000000000000)
  centralHi := (595304536459169020323/100000000000000000000)
  directionLo := (298642794322522763441/50000000000000000000)
  directionHi := (597285588645045526883/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree152.table
  base := (65960388610763967413072693845955486895463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-666564005103566795707031865804430000000000000)
      constant := (32144153341476222736930954317523821760473966967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree152.table
  base := (13192077722152793481751155928377071439943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (46827)
      previous := (0)
      next := (29040)
      square := (765332160521037786482523300770000000000000)
      linear := (-145743230131609877799209184845530000000000000)
      constant := (7088667970831663594674876400927174436202144785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298642794322522763441/50000000000000000000)
  centralHi := (597285588645045526883/100000000000000000000)
  directionLo := (599260091844310101883/100000000000000000000)
  directionHi := (149815022961077525471/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree153.table
  base := (16833821888051459114271201382849625258127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-670884353419896516626114156973370000000000000)
      constant := (32567765113214805684245035118331586697453877372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree153.table
  base := (8416910944025729556725887680665085017409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2787071890447353837177019149483130000000000000)
      constant := (136459458767516042675033359415694272629163540232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599260091844310101883/100000000000000000000)
  centralHi := (149815022961077525471/25000000000000000000)
  directionLo := (601228110579872520431/100000000000000000000)
  directionHi := (37576756911242032527/6250000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree154.table
  base := (859034719950100459798433689775575386873/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-675204701736226237545196448142310000000000000)
      constant := (32994153007103268924175990650461946342346852560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree154.table
  base := (68722777596008036781386136834032477618873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-23182003375158016497264989974390000000000000)
      constant := (1142527732127811407293573144641665724420413153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601228110579872520431/100000000000000000000)
  centralHi := (37576756911242032527/6250000000000000000)
  directionLo := (18849678385063961603/3125000000000000000)
  directionHi := (603189708322046771297/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree155.table
  base := (35061429368465747267560620645083922895469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-679525050052555958464278739311250000000000000)
      constant := (33423317023086031122160892135839390675996061242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree155.table
  base := (14024571747386298906646382177120572304787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2822972926340886155161108424319250000000000000)
      constant := (140043881905420173136086927229872018594227004735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18849678385063961603/3125000000000000000)
  centralHi := (603189708322046771297/100000000000000000000)
  directionLo := (302572473756217743553/50000000000000000000)
  directionHi := (605144947512435487107/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree156.table
  base := (35767765484909074766773989986973722822411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-683845398368885679383361030480190000000000000)
      constant := (33855257161108370417779013569141728450845916598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree156.table
  base := (17883882742454537383028411541359771421707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2840923444287652314153153061737310000000000000)
      constant := (141853537721155712009125472011265224701886333868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302572473756217743553/50000000000000000000)
  centralHi := (605144947512435487107/100000000000000000000)
  directionLo := (607093889587122052169/100000000000000000000)
  directionHi := (60709388958712205217/10000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree157.table
  base := (14592158857917843523384643001784178640581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-688165746685215400302443321649130000000000000)
      constant := (34289973421116405989853238885123621755989619145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree157.table
  base := (36480397144794608807917173769113734361897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2858873962234418473145197699155370000000000000)
      constant := (143674823034449950530649057901315534061324045714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607093889587122052169/100000000000000000000)
  centralHi := (60709388958712205217/10000000000000000000)
  directionLo := (38064787187449672407/6250000000000000000)
  directionHi := (609036594999194758513/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree158.table
  base := (37199324345621750218837776465094277139251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-692486095001545121221525612818070000000000000)
      constant := (34727465803057080125114183170515950372340627718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree158.table
  base := (18599662172810875109212244368448353748811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2876824480181184632137242336573430000000000000)
      constant := (145507737845084431355638570115667390160407253164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38064787187449672407/6250000000000000000)
  centralHi := (609036594999194758513/100000000000000000000)
  directionLo := (152743280810156593321/25000000000000000000)
  directionHi := (122194624648125274657/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree159.table
  base := (9481136771231967644872576666133624504399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-696806443317874842140607903987010000000000000)
      constant := (35167734306878140773779976573563012978937351928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree159.table
  base := (37924547084927870579176586158030441742933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2894774998127950791129286973991490000000000000)
      constant := (147352282152844014340205557245459735451546112746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152743280810156593321/25000000000000000000)
  centralHi := (122194624648125274657/20000000000000000000)
  directionLo := (306451766431765760523/50000000000000000000)
  directionHi := (612903532863531521047/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree160.table
  base := (618497045764600196310866038488451701213/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-701126791634204563059690195155950000000000000)
      constant := (35610778932528124576048451774210498012271089625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree160.table
  base := (3092485228823000981535279690369665856977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2912725516074716950121331611409550000000000000)
      constant := (149208455957516806655665748755035934357465308425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306451766431765760523/50000000000000000000)
  centralHi := (612903532863531521047/100000000000000000000)
  directionLo := (614827881500823369971/100000000000000000000)
  directionHi := (153706970375205842493/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree161.table
  base := (3151510333544928798072705703909207080007/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-705447139950534283978772486324890000000000000)
      constant := (36056599679956340344113776506294139447794856575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree161.table
  base := (7878775833862321995145614674945880920863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2930676034021483109113376248827610000000000000)
      constant := (151076259258894094778167583753712090245042167030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614827881500823369971/100000000000000000000)
  centralHi := (153706970375205842493/25000000000000000000)
  directionLo := (616746225886290239347/100000000000000000000)
  directionHi := (154186556471572559837/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree162.table
  base := (3211039080771738638121832486197526941959/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-709767488266864004897854777493830000000000000)
      constant := (36505196549112852984907930029071119083181075775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree162.table
  base := (40137988509646732976385718825938510472531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2948626551968249268105420886245670000000000000)
      constant := (152955692056770278292940570062760460151901253222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616746225886290239347/100000000000000000000)
  centralHi := (154186556471572559837/25000000000000000000)
  directionLo := (309329310937055957317/50000000000000000000)
  directionHi := (123731724374822382927/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree163.table
  base := (16355357351589739008633510533107335117109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-714087836583193725816937068662770000000000000)
      constant := (36956569539948467849330040730982358591287046905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree163.table
  base := (20444196689487173760739827711210325376353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2966577069915015427097465523663730000000000000)
      constant := (154846754350942805454544789869593032891057901572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309329310937055957317/50000000000000000000)
  centralHi := (123731724374822382927/20000000000000000000)
  directionLo := (620565124457834663633/100000000000000000000)
  directionHi := (310282562228917331817/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree164.table
  base := (83290187550020197342336879038878971560459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-718408184899523446736019359831710000000000000)
      constant := (37410718652414715494264822556201187009284909531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree164.table
  base := (83290187550020197342178835727747720219589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-2984527587861781586089510161081790000000000000)
      constant := (156749446141212110446718911484644828166911867109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620565124457834663633/100000000000000000000)
  centralHi := (310282562228917331817/50000000000000000000)
  directionLo := (31123289389441159553/5000000000000000000)
  directionHi := (622465787788823191061/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree165.table
  base := (84816179391006221930963222199046706205013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-722728533215853167655101651000650000000000000)
      constant := (37867643886463836844206339157401186506128982917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree165.table
  base := (84816179391006221930843280981605693069847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (7353)
      previous := (0)
      next := (4560)
      square := (120176124379336511927007791030000000000000)
      linear := (-24813868643045849132905411557850000000000000)
      constant := (1311270805184971506508631957827859655198214767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31123289389441159553/5000000000000000000)
  centralHi := (622465787788823191061/100000000000000000000)
  directionLo := (624360665194207047051/100000000000000000000)
  directionHi := (156090166298551761763/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree166.table
  base := (86354762276470614660830550472448196625507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-727048881532182888574183942169590000000000000)
      constant := (38327345242048768739796166654557222918000003763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree166.table
  base := (43177381138235307330369764364917242555787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-3020428623755313904073599435917910000000000000)
      constant := (160589718209257355327673358905204680144158663894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624360665194207047051/100000000000000000000)
  centralHi := (156090166298551761763/25000000000000000000)
  directionLo := (156562452298584579037/25000000000000000000)
  directionHi := (626249809194338316149/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree167.table
  base := (87905936202041491284841800231719010323123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-731369229848512609493266233338530000000000000)
      constant := (38789822719123129861056852299646586980518011907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree167.table
  base := (21976484050510372821193181884593852055911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-3038379141702080063065644073335970000000000000)
      constant := (162527298486648551291308237303254696206616993564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156562452298584579037/25000000000000000000)
  centralHi := (626249809194338316149/100000000000000000000)
  directionLo := (628133271519776755429/100000000000000000000)
  directionHi := (62813327151977675543/10000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree168.table
  base := (11183712645426243099525840965939782598119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-735689578164842330412348524507470000000000000)
      constant := (39255076317641207013553358396732521228667555768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree168.table
  base := (17893940232681988959230862623095781060649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-3056329659648846222057688710754030000000000000)
      constant := (164476508259366922811485570814493154062551044845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell231.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628133271519776755429/100000000000000000000)
  centralHi := (62813327151977675543/10000000000000000000)
  directionLo := (63001110312781792201/10000000000000000000)
  directionHi := (630011103127817922011/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree169.table
  base := (45523028578164392954336618460878071910773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (214137)
      previous := (0)
      next := (135960)
      square := (3531713306206041703694253892070000000000000)
      linear := (-740009926481172051331430815676410000000000000)
      constant := (39723106037557941766147836458946930929802781514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree169.table
  base := (4552302857816439295431673219280413797101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (889713)
      previous := (0)
      next := (551760)
      square := (14541311049899717943167942714630000000000000)
      linear := (-3074280177595612381049733348172090000000000000)
      constant := (166437347527226948412992637323519535101423375620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell231.Kernel169
