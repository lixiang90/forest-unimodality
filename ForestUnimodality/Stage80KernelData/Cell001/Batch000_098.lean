import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell001.Parameters
import ForestUnimodality.BinomialMassData.Q9_35.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_35.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_140.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree000.table
  base := (3903280090649386458991898521/1000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (2403887988104323886195956590000000000000)
      constant := (273229606345457052129432896470000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree000.table
  base := (3903280090649386458991898521/1000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (9615551952417295544783826360000000000000)
      constant := (1092918425381828208517731585880000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree001.table
  base := (7179273317162124369738876326170631377551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (10105275517550979053060800230000000000000)
      constant := (1403674821265083073378707010397443749999996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree001.table
  base := (888702009471792851780206133320436065051/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (39674219803628439751097545820000000000000)
      constant := (5559801953091333581305132795962274999999872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (27824028360353948747/100000000000000000000)
  directionHi := (6956007090088487187/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree002.table
  base := (5238997816888526032826214148118413903061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (3383335118371690902749904330000000000000)
      constant := (1021646573272553456063792418627209124999956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree002.table
  base := (2567820698610392078829396293208522002551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (12039575940335810688708307120000000000000)
      constant := (4005372196382034032878913256388962499999968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27824028360353948747/100000000000000000000)
  centralHi := (6956007090088487187/25000000000000000000)
  directionLo := (39349118267066184657/100000000000000000000)
  directionHi := (19674559133533092329/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree003.table
  base := (15099819114792660890871175050629337827259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-3338605280807597247560991570000000000000)
      constant := (734688386808127353812589162864837553535691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree003.table
  base := (14639739294627054133183190108916486811953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-15595067922956818373680931580000000000000)
      constant := (2848888075576973925108125083932131415142788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39349118267066184657/100000000000000000000)
  centralHi := (19674559133533092329/50000000000000000000)
  directionLo := (48192630791370401681/100000000000000000000)
  directionHi := (24096315395685200841/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree004.table
  base := (1333024268615781710434619478675747967023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-10060545679986885397871887470000000000000)
      constant := (519065511461346976990399505472893203073016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree004.table
  base := (2041816136279985147878675391380334687219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-43229711786249447436070170280000000000000)
      constant := (1988252261846030445050181673168727993474620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48192630791370401681/100000000000000000000)
  centralHi := (24096315395685200841/50000000000000000000)
  directionLo := (27824028360353948747/50000000000000000000)
  directionHi := (11129611344141579499/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree005.table
  base := (3643990216972049947669803373485291011109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-16782486079166173548182783370000000000000)
      constant := (357082286367683977521876429541558519088682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree005.table
  base := (6865914059564689913623140695515136422279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-70864355649542076498459408980000000000000)
      constant := (1348068320020339531719135346053466738766684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27824028360353948747/50000000000000000000)
  centralHi := (11129611344141579499/20000000000000000000)
  directionLo := (31108209410816721933/50000000000000000000)
  directionHi := (62216418821633443867/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree006.table
  base := (589445019109477737093306438331481103709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-23504426478345461698493679270000000000000)
      constant := (236213438495589851551098796533940592653928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree006.table
  base := (2169897569955393392584598075594823781377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-98498999512834705560848647680000000000000)
      constant := (875329169414631450457142208567170922299784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31108209410816721933/50000000000000000000)
  centralHi := (62216418821633443867/100000000000000000000)
  directionLo := (425966700447470291/625000000000000000)
  directionHi := (68154672071595246561/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree007.table
  base := (68619727799264626596219168680892620929/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-4318052411074964264114939310000000000000)
      constant := (20936271764467671787068451678649933860120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree007.table
  base := (2419536525072098898433602943801721720663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-18019091910875333517605412340000000000000)
      constant := (75520297163592454281000849457948208178564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425966700447470291/625000000000000000)
  centralHi := (68154672071595246561/100000000000000000000)
  directionLo := (73615459513504810743/100000000000000000000)
  directionHi := (9201932439188101343/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree008.table
  base := (152152999669935890256729629658593951817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-36948307276704037999115471070000000000000)
      constant := (80339955555159318941974469050168829112264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree008.table
  base := (941437104117735425680690206072597924413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-153768287239419963685627125080000000000000)
      constant := (275921634469432118012535068982229193184948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73615459513504810743/100000000000000000000)
  centralHi := (9201932439188101343/12500000000000000000)
  directionLo := (39349118267066184657/50000000000000000000)
  directionHi := (15739647306826473863/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree009.table
  base := (10751646823070583336185202158863018177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-43670247675883326149426366970000000000000)
      constant := (32114883852823742518809411783568575781346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree009.table
  base := (-26086096372472551151412200959148177421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-181402931102712592748016363780000000000000)
      constant := (94787445374100816473865489944555657803872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39349118267066184657/50000000000000000000)
  centralHi := (15739647306826473863/20000000000000000000)
  directionLo := (83472085081061846241/100000000000000000000)
  directionHi := (41736042540530923121/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree010.table
  base := (-925434415833552001854797038131130992623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-50392188075062614299737262870000000000000)
      constant := (-2191322172273887538415040488425418638527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree010.table
  base := (-55759953620735777957818803755601932561/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-209037574966005221810405602480000000000000)
      constant := (-31294649690923047420149844131959575639120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83472085081061846241/100000000000000000000)
  centralHi := (41736042540530923121/50000000000000000000)
  directionLo := (21996825824959678281/25000000000000000000)
  directionHi := (140779685279741941/160000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree011.table
  base := (-842763535760808454931913700552731614637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-57114128474241902450048158770000000000000)
      constant := (-25613621601792773020170831206167698234426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree011.table
  base := (-920200584877280395703915038952585664029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-236672218829297850872794841180000000000000)
      constant := (-114536895160867664051154770052913580299368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21996825824959678281/25000000000000000000)
  centralHi := (140779685279741941/160000000000000000)
  directionLo := (9228186222750161507/10000000000000000000)
  directionHi := (92281862227501615071/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree012.table
  base := (-2304954839337575008363330839130457595087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-63836068873421190600359054670000000000000)
      constant := (-40414842565789465025879857941392422159263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree012.table
  base := (-1215154884062388708177811851216325348359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-264306862692590479935184079880000000000000)
      constant := (-163958173240323450255582248748799536556728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9228186222750161507/10000000000000000000)
  centralHi := (92281862227501615071/100000000000000000000)
  directionLo := (96385261582740803363/100000000000000000000)
  directionHi := (24096315395685200841/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree013.table
  base := (-1409073089103596694615473601816558328281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-70558009272600478750669950570000000000000)
      constant := (-48281979551626551057546473414022716171538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree013.table
  base := (-583780897412984771140063076765735896629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-291941506555883108997573318580000000000000)
      constant := (-186218489359043856686741733505921178696420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96385261582740803363/100000000000000000000)
  centralHi := (24096315395685200841/25000000000000000000)
  directionLo := (100320960943220390607/100000000000000000000)
  directionHi := (6270060058951274413/6250000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree014.table
  base := (-3250766861590385283817722718645969943747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-11039992810254252414425835210000000000000)
      constant := (-7210379351262825635910277514521789606229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree014.table
  base := (-3331276186947431268931670469474020921691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-45653735774167962579994651040000000000000)
      constant := (-26605093164289341514946747487272585807348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100320960943220390607/100000000000000000000)
  centralHi := (6270060058951274413/6250000000000000000)
  directionLo := (20821596248865197793/20000000000000000000)
  directionHi := (52053990622162994483/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree015.table
  base := (-3621949410229162731686995378999566271159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-84001890070959055051291742370000000000000)
      constant := (-47924363803787740145959827250978747286791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree015.table
  base := (-3685951378524603753509261713353622208723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-347210794282468367122351795980000000000000)
      constant := (-167640857720719655111315005244809952909708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20821596248865197793/20000000000000000000)
  centralHi := (52053990622162994483/50000000000000000000)
  directionLo := (53880999232026851729/50000000000000000000)
  directionHi := (107761998464053703459/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree016.table
  base := (-3945955647288414860500523231542962512903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-90723830470138343201602638270000000000000)
      constant := (-41335933921550000396736271657605163132247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree016.table
  base := (-3996609123853255796170853772981149537567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-374845438145760996184741034680000000000000)
      constant := (-133115202234262289607406924880305309363132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53880999232026851729/50000000000000000000)
  centralHi := (107761998464053703459/100000000000000000000)
  directionLo := (27824028360353948747/25000000000000000000)
  directionHi := (111296113441415794989/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree017.table
  base := (-1058354091257216117260431101807906091089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-97445770869317631351913534170000000000000)
      constant := (-31228274632901977344088764238349593853444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree017.table
  base := (-42733490659465518342069577097068012551/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-402480082009053625247130273380000000000000)
      constant := (-84638215721233523801843159342033045999600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27824028360353948747/25000000000000000000)
  centralHi := (111296113441415794989/100000000000000000000)
  directionLo := (4588856314396827909/4000000000000000000)
  directionHi := (57360703929960348863/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree018.table
  base := (-898451118395593578216441877618621751883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-104167711268496919502224430070000000000000)
      constant := (-17989663335689031342826218612562329211335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree018.table
  base := (-2261813934507695006010387493169476343629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-430114725872346254309519512080000000000000)
      constant := (-23671404366969393997651195340434726702568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4588856314396827909/4000000000000000000)
  centralHi := (57360703929960348863/50000000000000000000)
  directionLo := (29511838700299638493/25000000000000000000)
  directionHi := (118047354801198553973/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree019.table
  base := (-945675932570490923837755627169910632437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-110889651667676207652535325970000000000000)
      constant := (-1909510431030907528721832904628104947065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree019.table
  base := (-950590147969576106048374487045219544327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-457749369735638883371908750780000000000000)
      constant := (48706211298060500481773867984184846559540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29511838700299638493/25000000000000000000)
  centralHi := (118047354801198553973/100000000000000000000)
  directionLo := (121282127824992566551/100000000000000000000)
  directionHi := (15160265978124070819/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree020.table
  base := (-4946190916563179605890651543042153921759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-117611592066855495802846221870000000000000)
      constant := (16796469474440501424292569150934457833809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree020.table
  base := (-4965382063284162293178904467092047886973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-485384013598931512434297989480000000000000)
      constant := (131698011845188934391935766129958614153292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121282127824992566551/100000000000000000000)
  centralHi := (15160265978124070819/12500000000000000000)
  directionLo := (31108209410816721933/25000000000000000000)
  directionHi := (124432837643266887733/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree021.table
  base := (-5148970639826821587742135290827996664319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-17761933209433540564736731110000000000000)
      constant := (5423927618801133917865144168204023349767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree021.table
  base := (-1290980613106561649186594523924610292249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-73288379637460591642383889740000000000000)
      constant := (32102268158060241961941589199943647268112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31108209410816721933/25000000000000000000)
  centralHi := (124432837643266887733/100000000000000000000)
  directionLo := (127505716099919998217/100000000000000000000)
  directionHi := (63752858049959999109/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree022.table
  base := (-5339164527952675929430965659104749861551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-131055472865214072103468013670000000000000)
      constant := (61483722070315927603869409459867256784001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree022.table
  base := (-5350787150472923417384331862734856166891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-540653301325516770559076466880000000000000)
      constant := (327325619414795943124492388621968191289364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127505716099919998217/100000000000000000000)
  centralHi := (63752858049959999109/50000000000000000000)
  directionLo := (1305062611231782193/1000000000000000000)
  directionHi := (130506261123178219301/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree023.table
  base := (-344912216967114200166400510058358982093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-137777413264393360253778909570000000000000)
      constant := (87255834054443327947174759858246558039088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree023.table
  base := (-5527611587063207304734468249197093536399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-568287945188809399621465705580000000000000)
      constant := (439206694561064830834865872521869666865796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1305062611231782193/1000000000000000000)
  centralHi := (130506261123178219301/100000000000000000000)
  directionLo := (133439352316132588233/100000000000000000000)
  directionHi := (66719676158066294117/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree024.table
  base := (-5688622165787716438084067013510978620503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-144499353663572648404089805470000000000000)
      constant := (115217253209515527953239453729962047595353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree024.table
  base := (-5695603144913513852184498410800880616141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-595922589052102028683854944280000000000000)
      constant := (560122455532810900560720189579027399236364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133439352316132588233/100000000000000000000)
  centralHi := (66719676158066294117/50000000000000000000)
  directionLo := (136309344143190493121/100000000000000000000)
  directionHi := (68154672071595246561/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree025.table
  base := (-5850257334436528215885099323112202493697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-151221294062751936554400701370000000000000)
      constant := (145318356081965483192794792867502077808847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree025.table
  base := (-1463913302260896031484202094274408392859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-623557232915394657746244182980000000000000)
      constant := (689898190866164903326387678001363819998544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136309344143190493121/100000000000000000000)
  centralHi := (68154672071595246561/50000000000000000000)
  directionLo := (27824028360353948747/20000000000000000000)
  directionHi := (17390017725221217967/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree026.table
  base := (-6004255847233295930677433929407746685879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-157943234461931224704711597270000000000000)
      constant := (177522154050954557329856264127020412391929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree026.table
  base := (-1502104972566648149488708037813726588587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-651191876778687286808633421680000000000000)
      constant := (828404910841744642627035273168038354547792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27824028360353948747/20000000000000000000)
  centralHi := (17390017725221217967/12500000000000000000)
  directionLo := (14187526355620384217/10000000000000000000)
  directionHi := (141875263556203842171/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree027.table
  base := (-6151180397798253668354248849866999077809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-164665174861110512855022493170000000000000)
      constant := (211801075129091280155658144652517045187359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree027.table
  base := (-615438909639500625122211197013977454587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-678826520641979915871022660380000000000000)
      constant := (975547377528306589797888696653104189009480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14187526355620384217/10000000000000000000)
  centralHi := (141875263556203842171/100000000000000000000)
  directionLo := (28915578474822241009/20000000000000000000)
  directionHi := (72288946187055602523/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree028.table
  base := (-6291450454188192274663479839042996319359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-24483873608612828715047627010000000000000)
      constant := (35447795054513271461221654638699025764487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree028.table
  base := (-6293919617229808403964945018884027692949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-100923023500753220704773128440000000000000)
      constant := (161607895446408287780941957167247224597428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28915578474822241009/20000000000000000000)
  centralHi := (72288946187055602523/50000000000000000000)
  directionLo := (147230919027009621487/100000000000000000000)
  directionHi := (9201932439188101343/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree029.table
  base := (-401586171365603819892527705060392719053/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-178109055659469089155644284970000000000000)
      constant := (286507301261578498483446074764652108262448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree029.table
  base := (-1285455281404379685036547708969536706593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-734095808368565173995801137780000000000000)
      constant := (1295476651598222640309266463238354027538860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147230919027009621487/100000000000000000000)
  centralHi := (9201932439188101343/6250000000000000000)
  directionLo := (37459244579722610709/25000000000000000000)
  directionHi := (149836978318890442837/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree030.table
  base := (-3276599216910675229080432977463321933533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-184830996058648377305955180870000000000000)
      constant := (326907857290152252231511009348594450513766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree030.table
  base := (-6554655153449835466921998335163571452159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-761730452231857803058190376480000000000000)
      constant := (1468173173163402873524791851577939995376836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37459244579722610709/25000000000000000000)
  centralHi := (149836978318890442837/100000000000000000000)
  directionLo := (152398479736293385003/100000000000000000000)
  directionHi := (38099619934073346251/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree031.table
  base := (-6675083414779714681274272556011412501811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-191552936457827665456266076770000000000000)
      constant := (369327713118167896511239676163440787411261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree031.table
  base := (-6676200413856505778077170536927779375557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-789365096095150432120579615180000000000000)
      constant := (1649316499581193009329858420358655242390828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152398479736293385003/100000000000000000000)
  centralHi := (38099619934073346251/25000000000000000000)
  directionLo := (154917633535150563041/100000000000000000000)
  directionHi := (77458816767575281521/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree032.table
  base := (-424447711433962655643307895143738226153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-198274876857006953606576972670000000000000)
      constant := (413760513532911644891691176543309230696048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree032.table
  base := (-1698004750660857507523828920600772376513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-816999739958443061182968853880000000000000)
      constant := (1838885695228894996120842305256994456813808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154917633535150563041/100000000000000000000)
  centralHi := (77458816767575281521/50000000000000000000)
  directionLo := (157396473068264738629/100000000000000000000)
  directionHi := (15739647306826473863/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree033.table
  base := (-6901535104667105450344411204473761100893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-204996817256186241756887868570000000000000)
      constant := (460201516983003610681613896904785706056243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree033.table
  base := (-6902189873029097048570935875870206381009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-844634383821735690245358092580000000000000)
      constant := (2036865285275685024081221093833939549322236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157396473068264738629/100000000000000000000)
  centralHi := (15739647306826473863/10000000000000000000)
  directionLo := (79918436997552023001/50000000000000000000)
  directionHi := (159836873995104046003/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree034.table
  base := (-875783850215647694061980877057860926503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-211718757655365529907198764470000000000000)
      constant := (508647184601500252318718966365318516810824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree034.table
  base := (-1751692852748098180560243268844640459633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-872269027685028319307747331280000000000000)
      constant := (2243243826069701459018554162311801879647728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79918436997552023001/50000000000000000000)
  centralHi := (159836873995104046003/100000000000000000000)
  directionLo := (20280071361254404529/12500000000000000000)
  directionHi := (162240570890035236233/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree035.table
  base := (-7105424401703821052984756311956498135823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-31205814007792116865358522910000000000000)
      constant := (79870696276668321035338254256304513049239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree035.table
  base := (-1421161363796117851189974658445807377717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-128557667364045849767162367140000000000000)
      constant := (351144692847325564111904298925086967119620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20280071361254404529/12500000000000000000)
  centralHi := (162240570890035236233/100000000000000000000)
  directionLo := (329218343334160709/200000000000000000)
  directionHi := (164609171667080354501/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree036.table
  base := (-359951809794395243416908519286985111903/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-225162638453724106207820556270000000000000)
      constant := (611542610715578430557735803746754590335060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree036.table
  base := (-1799832022397214448123427582720315943843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-927538315411613577432525808680000000000000)
      constant := (2681166086311763949387518418651272300027088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329218343334160709/200000000000000000)
  centralHi := (164609171667080354501/100000000000000000000)
  directionLo := (166944170162123692483/100000000000000000000)
  directionHi := (41736042540530923121/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree037.table
  base := (-7287136310367618869105408476030008442567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-231884578852903394358131452170000000000000)
      constant := (665988918759781694592906395550529586314217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree037.table
  base := (-455459933654142309005864915935884840449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-955172959274906206494915047380000000000000)
      constant := (2912698886943937052835733665965565140351936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166944170162123692483/100000000000000000000)
  centralHi := (41736042540530923121/25000000000000000000)
  directionLo := (169246957152316010061/100000000000000000000)
  directionHi := (84623478576158005031/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree038.table
  base := (-1473949458548035444060118974065129632617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-238606519252082682508442348070000000000000)
      constant := (722432693237024545267187465118043240008835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree038.table
  base := (-7369916969025784423106497428568379476791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-982807603138198835557304286080000000000000)
      constant := (3152607801558862467506152958262597622548964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169246957152316010061/100000000000000000000)
  centralHi := (84623478576158005031/50000000000000000000)
  directionLo := (34303766008714362313/20000000000000000000)
  directionHi := (85759415021785905783/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree039.table
  base := (-14544699296392944682495185894307742783/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-245328459651261970658753243970000000000000)
      constant := (780873106206674202560402537595607349060096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree039.table
  base := (-3723507635081881163942340064944215346697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1010442247001491464619693524780000000000000)
      constant := (3400890264732849302121589573810367584094776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34303766008714362313/20000000000000000000)
  centralHi := (85759415021785905783/50000000000000000000)
  directionLo := (6950440056711627019/4000000000000000000)
  directionHi := (43440250354447668869/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree040.table
  base := (-7518565233826305979981196009052014036403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-252050400050441258809064139870000000000000)
      constant := (841309536230167535238768249076451312216253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree040.table
  base := (-1503732719101322094155970864827954280151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1038076890864784093682082763480000000000000)
      constant := (3657544364755123193461155869828604805452020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6950440056711627019/4000000000000000000)
  centralHi := (43440250354447668869/25000000000000000000)
  directionLo := (175974606599677426249/100000000000000000000)
  directionHi := (140779685279741941/80000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree041.table
  base := (-7584794413601038495142477400174960376459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-258772340449620546959375035770000000000000)
      constant := (903741515914070731308950497779426941553509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree041.table
  base := (-1896217308451759137785411420106361638781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1065711534728076722744472002180000000000000)
      constant := (3922568673030153432452325215173112475195696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175974606599677426249/100000000000000000000)
  centralHi := (140779685279741941/80000000000000000)
  directionLo := (712642841508805333/400000000000000000)
  directionHi := (178160710377201333251/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree042.table
  base := (-3822790385890457037258556296263937571263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-37927754406971405015669418810000000000000)
      constant := (138309813259415839577536907840304874002318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree042.table
  base := (-7645637651401583224254911719318948184491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-156192311227338478829551605840000000000000)
      constant := (599423159736568236951323647973069450834252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (712642841508805333/400000000000000000)
  centralHi := (178160710377201333251/100000000000000000000)
  directionLo := (45080078247150089991/25000000000000000000)
  directionHi := (36064062597720071993/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree043.table
  base := (-3850464874879979722413352506157901772227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-272216221247979123259996827570000000000000)
      constant := (1034590800307380662830833252500525626321754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree043.table
  base := (-7700972966447549063122071078777511726839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1120980822454661980869250479580000000000000)
      constant := (4477723892973765351773502778704107701539556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45080078247150089991/25000000000000000000)
  centralHi := (36064062597720071993/20000000000000000000)
  directionLo := (36490871094291282501/20000000000000000000)
  directionHi := (91227177735728206253/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree044.table
  base := (-1550169096165494704078393217190807152987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-278938161647158411410307723470000000000000)
      constant := (1103007635857304441871460330740252247518185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree044.table
  base := (-7750878299013938195448764942841928276479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1148615466317954609931639718280000000000000)
      constant := (4767853385949991702764731271778982057810116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36490871094291282501/20000000000000000000)
  centralHi := (91227177735728206253/50000000000000000000)
  directionLo := (9228186222750161507/5000000000000000000)
  directionHi := (184563724455003230141/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree045.table
  base := (-974416390067420533923222493838349637393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-285660102046337699560618619370000000000000)
      constant := (1173419044843442723626168266875366942141944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree045.table
  base := (-3897678014777222082714862414361188094973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1176250110181247238994028956980000000000000)
      constant := (5066350130515732776970783637662914266770584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9228186222750161507/5000000000000000000)
  centralHi := (184563724455003230141/100000000000000000000)
  directionLo := (93324628232450165799/50000000000000000000)
  directionHi := (186649256464900331599/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree046.table
  base := (-7834389093011374558627136015125801767571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-292382042445516987710929515270000000000000)
      constant := (1245824908484124107914826579886835713389021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree046.table
  base := (-15668815979536156789439412345476846701/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1203884754044539868056418195680000000000000)
      constant := (5373213767657982335747327810837269023302000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93324628232450165799/50000000000000000000)
  centralHi := (186649256464900331599/100000000000000000000)
  directionLo := (94355870899878189667/50000000000000000000)
  directionHi := (37742348359951275867/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree047.table
  base := (-1967005318640175743209643080039993119397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-299103982844696275861240411170000000000000)
      constant := (1320225134839805863792030905768161348598188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree047.table
  base := (-1573607120712601984685844659705242366407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1231519397907832497118807434380000000000000)
      constant := (5688444018290739247232702983869362480921140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94355870899878189667/50000000000000000000)
  centralHi := (37742348359951275867/20000000000000000000)
  directionLo := (95375964015174834731/50000000000000000000)
  directionHi := (190751928030349669463/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree048.table
  base := (-7896229130661340487375540736920459179719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-305825923243875564011551307070000000000000)
      constant := (1396619652102262433563364102834897500193769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree048.table
  base := (-7896239991196906567550933401371583673063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1259154041771125126181196673080000000000000)
      constant := (6012040662843500619492348346483169600079652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95375964015174834731/50000000000000000000)
  centralHi := (190751928030349669463/100000000000000000000)
  directionLo := (192770523165481606727/100000000000000000000)
  directionHi := (24096315395685200841/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree049.table
  base := (-3959506909054522386244989150312899555437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-44649694806150693165980314710000000000000)
      constant := (210715486226928813055211608051619406223882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree049.table
  base := (-7919022046241018771555146821197516730609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-183826955090631107891940844540000000000000)
      constant := (906286218025185909344297581721969531542948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192770523165481606727/100000000000000000000)
  centralHi := (24096315395685200841/12500000000000000000)
  directionLo := (19476819852247764123/10000000000000000000)
  directionHi := (194768198522477641231/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree050.table
  base := (-7936376261259628231283599819206954106113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-319269804042234140312173098870000000000000)
      constant := (1555391344005088829509398340758859248800463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree050.table
  base := (-7936382492486874133036370517948868837309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1314423329497710384305975150480000000000000)
      constant := (6684332466426002075857383796432021707887436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19476819852247764123/10000000000000000000)
  centralHi := (194768198522477641231/100000000000000000000)
  directionLo := (196745591335330923287/100000000000000000000)
  directionHi := (24593198916916365411/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree051.table
  base := (-3974158604472427086296643100324237381719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-325991744441413428462483994770000000000000)
      constant := (1637768436659267445799108191536224736591538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree051.table
  base := (-7948321926048612649718913915379420391849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1342057973361003013368364389180000000000000)
      constant := (7033027366754231311280285872562133603197596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196745591335330923287/100000000000000000000)
  centralHi := (24593198916916365411/12500000000000000000)
  directionLo := (24837913391151773933/12500000000000000000)
  directionHi := (39740661425842838293/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree052.table
  base := (-1988709319246690566959386115295666896143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-332713684840592716612794890670000000000000)
      constant := (1722139651375757596356103964898049288355972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree052.table
  base := (-497177552908570398482182937552778027779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1369692617224295642430753627880000000000000)
      constant := (7390088129237254229072807902922488104885056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24837913391151773933/12500000000000000000)
  centralHi := (39740661425842838293/20000000000000000000)
  directionLo := (100320960943220390607/50000000000000000000)
  directionHi := (40128384377288156243/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree053.table
  base := (-7955936979976905936934390902962616896319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-339435625239772004763105786570000000000000)
      constant := (1808504962939573163604402862038831772080369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree053.table
  base := (-795593968016616410223955033413696798501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1397327261087588271493142866580000000000000)
      constant := (7755514670337176066156782337793654274938040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100320960943220390607/50000000000000000000)
  centralHi := (40128384377288156243/20000000000000000000)
  directionLo := (40512396805166877229/20000000000000000000)
  directionHi := (101280992012917193073/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree054.table
  base := (-3975808377526202921755710266905787056217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-346157565638951292913416682470000000000000)
      constant := (1896864349930995235026252727575232868490734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree054.table
  base := (-7951618796900867775703502245668236844547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1424961904950880900555532105280000000000000)
      constant := (8129306917540829001035708384415025578468788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40512396805166877229/20000000000000000000)
  centralHi := (101280992012917193073/50000000000000000000)
  directionLo := (102232008107392869841/50000000000000000000)
  directionHi := (204464016214785739683/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree055.table
  base := (-3970938489852200922049734977426972637027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-352879506038130581063727578370000000000000)
      constant := (1987217793852957957651642568052156681571354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree055.table
  base := (-7941878523206036567644858446688762705379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1452596548814173529617921343980000000000000)
      constant := (8511464806861112396088123203381502509745716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102232008107392869841/50000000000000000000)
  centralHi := (204464016214785739683/100000000000000000000)
  directionLo := (206348517030963774081/100000000000000000000)
  directionHi := (103174258515481887041/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree056.table
  base := (-7926717985135687586025377306052939035963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-51371635205329981316291210610000000000000)
      constant := (297080754068074920394508187801629426748259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree056.table
  base := (-39633595757716313731332069239549911397/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-211461598953923736954330083240000000000000)
      constant := (1271712611567936309535182713170520496176800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206348517030963774081/100000000000000000000)
  centralHi := (103174258515481887041/50000000000000000000)
  directionLo := (208215962488651977931/100000000000000000000)
  directionHi := (52053990622162994483/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree057.table
  base := (-395307003314889144249779384743569780547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-366323386836489157364349370170000000000000)
      constant := (2173906789349070219386381156987301615063940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree057.table
  base := (-7906140947464940702806169612874976605181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1507865836540758787742699821380000000000000)
      constant := (9300877287835885012327527522797004585384524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208215962488651977931/100000000000000000000)
  centralHi := (52053990622162994483/25000000000000000000)
  directionLo := (105033403721475089147/50000000000000000000)
  directionHi := (42013361488590035659/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree058.table
  base := (-788014348944971877036939944635816491783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-373045327235668445514660266070000000000000)
      constant := (2270242313423902767087508477252449919026330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree058.table
  base := (-7880144154930966224681122160246991571983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1535500480404051416805089060080000000000000)
      constant := (9708131779625965358498137497133589651891332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105033403721475089147/50000000000000000000)
  centralHi := (42013361488590035659/20000000000000000000)
  directionLo := (21190148688357825979/10000000000000000000)
  directionHi := (211901486883578259791/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree059.table
  base := (-7848728497866253484209393507045469490301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-379767267634847733664971161970000000000000)
      constant := (2368571838780558932003872809026771994975251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree059.table
  base := (-7848729000310017681212573551176461646127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1563135124267344045867478298780000000000000)
      constant := (10123751711977534244871133711217913517359108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21190148688357825979/10000000000000000000)
  centralHi := (211901486883578259791/100000000000000000000)
  directionLo := (4274408342574165907/2000000000000000000)
  directionHi := (213720417128708295351/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree060.table
  base := (-3905947658081692131033315207980565032287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-386489208034027021815282057870000000000000)
      constant := (2468895354412854849593472185897904626835874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree060.table
  base := (-7811895695406369529397752909763288188103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1590769768130636674929867537480000000000000)
      constant := (10547737043376953877875059256726395515131812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4274408342574165907/2000000000000000000)
  centralHi := (213720417128708295351/100000000000000000000)
  directionLo := (215523996928107406917/100000000000000000000)
  directionHi := (107761998464053703459/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree061.table
  base := (-7769644153589921288632757959418078127043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-393211148433206309965592953770000000000000)
      constant := (2571212850067598820806415866336514171774893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree061.table
  base := (-3884822219881980229295014307484690058201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1618404411993929303992256776180000000000000)
      constant := (10980087734713612274396653931382501497185208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215523996928107406917/100000000000000000000)
  centralHi := (107761998464053703459/50000000000000000000)
  directionLo := (108656304241935994331/50000000000000000000)
  directionHi := (217312608483871988663/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree062.table
  base := (-1544395041309030937427157680171290431187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-399933088832385598115903849670000000000000)
      constant := (2675524316121225629604531249434033844359185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree062.table
  base := (-7721975422433607168382890665352242532487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1646039055857221933054646014880000000000000)
      constant := (11420803748933549361315593695468960463632548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108656304241935994331/50000000000000000000)
  centralHi := (217312608483871988663/100000000000000000000)
  directionLo := (219086618396154932009/100000000000000000000)
  directionHi := (21908661839615493201/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree063.table
  base := (-3834444330258265115604491849671979438457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-58093575604509269466602106510000000000000)
      constant := (397404249069264347582826928456592287861602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree063.table
  base := (-7668888823340684128139738012357691130343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-239096242817216366016719321940000000000000)
      constant := (1695697864395913106090950336357484648350396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219086618396154932009/100000000000000000000)
  centralHi := (21908661839615493201/10000000000000000000)
  directionLo := (220846378540514432231/100000000000000000000)
  directionHi := (27605797317564304029/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree064.table
  base := (-59456130402984267923892330180304522489/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-413376969630744174416525641470000000000000)
      constant := (2890129123530654250935299769621130034948992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree064.table
  base := (-7610384814354752501954498388768883208537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1701308343583807191179424492280000000000000)
      constant := (12327331606540705430197420072857298891126748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220846378540514432231/100000000000000000000)
  centralHi := (27605797317564304029/12500000000000000000)
  directionLo := (222592226882831589977/100000000000000000000)
  directionHi := (111296113441415794989/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree065.table
  base := (-1509292693516979179379637974415918818019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-420098910029923462566836537370000000000000)
      constant := (3000422448034311805160944869488099889585345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree065.table
  base := (-1509292712027235542806080410109490499319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1728942987447099820241813730980000000000000)
      constant := (12793143383968058800854063720365199310667380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222592226882831589977/100000000000000000000)
  centralHi := (111296113441415794989/50000000000000000000)
  directionLo := (224324488237142213303/100000000000000000000)
  directionHi := (28040561029642776663/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree066.table
  base := (-7477125149062201988935170505085848512769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-426820850429102750717147433270000000000000)
      constant := (3112709709129512891216216471838793422874319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree066.table
  base := (-7477125218815260810274327251995941650559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1756577631310392449304202969680000000000000)
      constant := (13267320352059912849608835159182795436490436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224324488237142213303/100000000000000000000)
  centralHi := (28040561029642776663/12500000000000000000)
  directionLo := (1412771718569972561/625000000000000000)
  directionHi := (226043474971195609761/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree067.table
  base := (-462648118124121637051449667565084791001/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-433542790828282038867458329170000000000000)
      constant := (3226990899271627469600866885244973523855216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree067.table
  base := (-7402369942545006077720583228305326457113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1784212275173685078366592208380000000000000)
      constant := (13749862480994278736203009779212656014405852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1412771718569972561/625000000000000000)
  centralHi := (226043474971195609761/100000000000000000000)
  directionLo := (1821995901312646829/800000000000000000)
  directionHi := (113874743832040426813/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree068.table
  base := (-73221978383631943109354974589198799067/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-440264731227461327017769225070000000000000)
      constant := (3343266011208309315998607591816925884571700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree068.table
  base := (-1464439575591603077068756604813201387417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1811846919036977707428981447080000000000000)
      constant := (14240769742031166494317563423715062640331340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1821995901312646829/800000000000000000)
  centralHi := (113874743832040426813/50000000000000000000)
  directionLo := (229442815719841395451/100000000000000000000)
  directionHi := (57360703929960348863/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree069.table
  base := (-361830456836401615109491905962543591823/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-446986671626640615168080120970000000000000)
      constant := (3461535037955388218422468386808707280013460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree069.table
  base := (-7236609166550149268080465738312876422927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1839481562900270336491370685780000000000000)
      constant := (14740042107437387459104934429279176221106308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229442815719841395451/100000000000000000000)
  centralHi := (57360703929960348863/25000000000000000000)
  directionLo := (57780934485156346541/25000000000000000000)
  directionHi := (46224747588125077233/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree070.table
  base := (-3572801961275429056700140702170916311317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-64815516003688557616913002410000000000000)
      constant := (511685424682402096782651442549607171641562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree070.table
  base := (-1429120789001559254984275202585713445063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-266730886680508995079108560640000000000000)
      constant := (2178239935774629924994705263728000117691180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57780934485156346541/25000000000000000000)
  centralHi := (46224747588125077233/20000000000000000000)
  directionLo := (46558504612517210643/20000000000000000000)
  directionHi := (7274766345705814163/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree071.table
  base := (-3524591164291946580502404871465743292341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-460430552424999191468701912770000000000000)
      constant := (3704054809167729843761421585924357157350582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree071.table
  base := (-7049182345491307375211229238643412901329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1894750850626855594616149163180000000000000)
      constant := (15763682045082803751900006457582391071339516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46558504612517210643/20000000000000000000)
  centralHi := (7274766345705814163/3125000000000000000)
  directionLo := (7326544695545281093/3125000000000000000)
  directionHi := (234449430257448994977/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree072.table
  base := (-6947344483157135212366300253825174950249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-467152492824178479619012808670000000000000)
      constant := (3828305540839963826670271872218566427437799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree072.table
  base := (-6947344495883984322699581840181583370783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1922385494490148223678538401880000000000000)
      constant := (16288049566353443146181230204492409659326532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7326544695545281093/3125000000000000000)
  centralHi := (234449430257448994977/100000000000000000000)
  directionLo := (29511838700299638493/12500000000000000000)
  directionHi := (47218941920479421589/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree073.table
  base := (-6840090510435464295912158169171701985549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-473874433223357767769323704570000000000000)
      constant := (3954550161709437504812168100354586602708099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree073.table
  base := (-3420045260006833521638646093782161306107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1950020138353440852740927640580000000000000)
      constant := (16820782089964071032331999846301892768006056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29511838700299638493/12500000000000000000)
  centralHi := (47218941920479421589/20000000000000000000)
  directionLo := (237728602520685343841/100000000000000000000)
  directionHi := (118864301260342671921/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree074.table
  base := (-336371026532249571415076850202274945919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-480596373622537055919634600470000000000000)
      constant := (4082788665885071438370811748093770552999380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree074.table
  base := (-105115945903941084446081022262569683111/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-1977654782216733481803316879280000000000000)
      constant := (17361879592400200132301769654784325895055616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237728602520685343841/100000000000000000000)
  centralHi := (118864301260342671921/50000000000000000000)
  directionLo := (59837835548795850719/25000000000000000000)
  directionHi := (239351342195183402877/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree075.table
  base := (-826166832534347523063197787016324030897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-487318314021716344069945496370000000000000)
      constant := (4213021047658901512172616684089600979888376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree075.table
  base := (-660933466569700587975339794587005660097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2005289426080026110865706117980000000000000)
      constant := (17911342050867552889335864896721968906209880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59837835548795850719/25000000000000000000)
  centralHi := (239351342195183402877/100000000000000000000)
  directionLo := (240963153956852008409/100000000000000000000)
  directionHi := (24096315395685200841/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree076.table
  base := (-1621458253064651235868102144987407194069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-494040254420895632220256392270000000000000)
      constant := (4345247301497172781649125296150468189962476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree076.table
  base := (-6485833016337216168328913983227224182443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2032924069943318739928095356680000000000000)
      constant := (18469169443259442242344244662551464060241172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240963153956852008409/100000000000000000000)
  centralHi := (24096315395685200841/10000000000000000000)
  directionLo := (121282127824992566551/50000000000000000000)
  directionHi := (242564255649985133103/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree077.table
  base := (-3178457848070155740697488183677677048313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-71537456402867845767223898310000000000000)
      constant := (639923917433176686252411788456512521323618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree077.table
  base := (-1589228924801936034915475319385416122883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-294365530543801624141497799340000000000000)
      constant := (2719337392589518707561031439300333394237104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121282127824992566551/50000000000000000000)
  centralHi := (242564255649985133103/100000000000000000000)
  directionLo := (2441548579758943183/1000000000000000000)
  directionHi := (244154857975894318301/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree078.table
  base := (-1555645704556380482381902487149848409101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-507484135219254208520878184070000000000000)
      constant := (4615681404055118094094426463002629711816204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree078.table
  base := (-6222582820532097617202210423513645804327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2088193357669903998052873834080000000000000)
      constant := (19609918944649311487688620417813325422351908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2441548579758943183/1000000000000000000)
  centralHi := (244154857975894318301/100000000000000000000)
  directionLo := (122867582408285085319/50000000000000000000)
  directionHi := (245735164816570170639/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree079.table
  base := (-1520708620430451820141484801039622706403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-514206075618433496671189079970000000000000)
      constant := (4753889242508645673989671263428233949545012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree079.table
  base := (-6082834483455979374190747178292357816313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2115828001533196627115263072780000000000000)
      constant := (20192841012610926103073228162283197868002652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122867582408285085319/50000000000000000000)
  centralHi := (245735164816570170639/100000000000000000000)
  directionLo := (247305373539728584513/100000000000000000000)
  directionHi := (123652686769864292257/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree080.table
  base := (-5937670786868984693596636475134655728751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-520928016017612784821499975870000000000000)
      constant := (4894090932481068502657369975758401869291201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree080.table
  base := (-1187534157634520497903029122673938267199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2143462645396489256177652311480000000000000)
      constant := (20784127932373605035619067030499540498144980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247305373539728584513/100000000000000000000)
  centralHi := (123652686769864292257/50000000000000000000)
  directionLo := (31108209410816721933/12500000000000000000)
  directionHi := (49773135057306755093/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree081.table
  base := (-4521165493016285248984687613192135019/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-527649956416792072971810871770000000000000)
      constant := (5036286469200090823543568379208589291608320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree081.table
  base := (-1157418366408131849887377601692587174167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2171097289259781885240041550180000000000000)
      constant := (21383779684855044597218886495637764569316340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31108209410816721933/12500000000000000000)
  centralHi := (49773135057306755093/20000000000000000000)
  directionLo := (62604063810796384681/25000000000000000000)
  directionHi := (10016650209727421549/4000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree082.table
  base := (-2815548854479675199547061818399627253189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-534371896815971361122121767670000000000000)
      constant := (5180475848027276506330638696032836529187478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree082.table
  base := (-1407774427423920784473474768401894804877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2198731933123074514302430788880000000000000)
      constant := (21991796251506680225020853314530914472976432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62604063810796384681/25000000000000000000)
  centralHi := (10016650209727421549/4000000000000000000)
  directionLo := (251957292897463140019/100000000000000000000)
  directionHi := (12597864644873157001/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree083.table
  base := (-2734844256301068256205147870793136163039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-541093837215150649272432663570000000000000)
      constant := (5326659064452781388114588975486272656022178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree083.table
  base := (-5469688513155414152252791052328869138879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2226366576986367143364820027580000000000000)
      constant := (22608177614293034879541111487448041648779716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251957292897463140019/100000000000000000000)
  centralHi := (12597864644873157001/5000000000000000000)
  directionLo := (10139558491249276127/4000000000000000000)
  directionHi := (31686120285153987897/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree084.table
  base := (-42422914652032039623419470420183694249/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-78259396802047133917534794210000000000000)
      constant := (782119444870054313667967409678339267532125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree084.table
  base := (-1060572866383935677301198020554532711511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-322000174407094253203887038040000000000000)
      constant := (3318989107953163235193877926770365420388460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10139558491249276127/4000000000000000000)
  centralHi := (31686120285153987897/12500000000000000000)
  directionLo := (127505716099919998217/50000000000000000000)
  directionHi := (51002286439967999287/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree085.table
  base := (-5130625252752965476565851050318247374209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-554537718013509225573054455370000000000000)
      constant := (5625006992672760450974092024514405878663759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree085.table
  base := (-1026125050613043182017020764149282928053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2281635864712952401489598504980000000000000)
      constant := (23866034658576962471860360225586202730508060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127505716099919998217/50000000000000000000)
  centralHi := (51002286439967999287/20000000000000000000)
  directionLo := (5130497328985227031/2000000000000000000)
  directionHi := (256524866449261351551/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree086.table
  base := (-61912142013766270107172123850808667561/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-561259658412688513723365351270000000000000)
      constant := (5777171696047060261272386547052830023160880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree086.table
  base := (-1238242840333957699144176781277974115369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2309270508576245030551987743680000000000000)
      constant := (24507510306397708757627787017932068293550704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5130497328985227031/2000000000000000000)
  centralHi := (256524866449261351551/100000000000000000000)
  directionLo := (64507356005443844779/25000000000000000000)
  directionHi := (258029424021775379117/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree087.table
  base := (-4769902739052058789839239754888748328127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-567981598811867801873676247170000000000000)
      constant := (5931330220170630399967141015786451331921777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree087.table
  base := (-1192475684807047387166013070775517026267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2336905152439537659614376982380000000000000)
      constant := (25157350682965034869133508420052494651406672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64507356005443844779/25000000000000000000)
  centralHi := (258029424021775379117/100000000000000000000)
  directionLo := (64881314825228637389/25000000000000000000)
  directionHi := (259525259300914549557/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree088.table
  base := (-4581419466941298836520229488417093019917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-574703539211047090023987143070000000000000)
      constant := (6087482561107003838066614954731562442024067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree088.table
  base := (-143169358346048625994053975581335132517/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2364539796302830288676766221080000000000000)
      constant := (25815555772534013088746857198865866048853376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64881314825228637389/25000000000000000000)
  centralHi := (259525259300914549557/100000000000000000000)
  directionLo := (261012522246356438601/100000000000000000000)
  directionHi := (130506261123178219301/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree089.table
  base := (-4387521623016419790128174513392475074031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-581425479610226378174298038970000000000000)
      constant := (6245628715022058071536748029055768721372481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree089.table
  base := (-4387521623115720076636488839255889685121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2392174440166122917739155459780000000000000)
      constant := (26482125559768860609665773000474345621716284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261012522246356438601/100000000000000000000)
  centralHi := (130506261123178219301/50000000000000000000)
  directionLo := (131245679284693497687/50000000000000000000)
  directionHi := (2099930868555095963/800000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree090.table
  base := (-4188209283510804458429946594627200901063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-588147420009405666324608934870000000000000)
      constant := (6405768678180357342796963522283267155847913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree090.table
  base := (-4188209283585351435267523747294855377909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2419809084029415546801544698480000000000000)
      constant := (27157060029728366160474111250840208345929836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131245679284693497687/50000000000000000000)
  centralHi := (2099930868555095963/800000000000000000)
  directionLo := (131980954949758069687/50000000000000000000)
  directionHi := (422339055839225823/160000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree091.table
  base := (-398348252271503190686863287014074782887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-84981337201226422067845690110000000000000)
      constant := (938271778134523325377221452093014765197910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree091.table
  base := (-3983482522770989512188122261606662068549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-349634818270386882266276276740000000000000)
      constant := (3977194166835996573984679292494513462080628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131980954949758069687/50000000000000000000)
  centralHi := (422339055839225823/160000000000000000)
  directionLo := (132712156971392467559/50000000000000000000)
  directionHi := (265424313942784935119/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree092.table
  base := (-3773341413044862291651566265990569823849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-601591300807764242625230726670000000000000)
      constant := (6732030017757603628413348642782462078631399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree092.table
  base := (-150933656523474451572820131917544819569/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2475078371756000804926323175880000000000000)
      constant := (28532022959946501693464949482852030384111900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132712156971392467559/50000000000000000000)
  centralHi := (265424313942784935119/100000000000000000000)
  directionLo := (266878704632265176467/100000000000000000000)
  directionHi := (66719676158066294117/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree093.table
  base := (-3557786025106185553826556155418862728431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-608313241206943530775541622570000000000000)
      constant := (6898151387168489788004016297388475726306881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree093.table
  base := (-1778893012568852209862620450534192027109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2502713015619293433988712414580000000000000)
      constant := (29232051392173414607190822044235096725373272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266878704632265176467/100000000000000000000)
  centralHi := (66719676158066294117/25000000000000000000)
  directionLo := (268325212271216919667/100000000000000000000)
  directionHi := (67081303067804229917/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree094.table
  base := (-1668408213878553866632255161556818872679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-615035181606122818925852518470000000000000)
      constant := (7066266551800274560458878647019431750477458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree094.table
  base := (-3336816427780759042462404284294981632331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2530347659482586063051101653280000000000000)
      constant := (29940444451036695691814599165804183600063124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268325212271216919667/100000000000000000000)
  centralHi := (67081303067804229917/25000000000000000000)
  directionLo := (269763963669337050053/100000000000000000000)
  directionHi := (134881981834668525027/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree095.table
  base := (-3110432688167334343976139376589171795211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-621757122005302107076163414370000000000000)
      constant := (7236375508361642375591410871907130582034661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree095.table
  base := (-3110432688185080070967365827521876305429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2557982303345878692113490891980000000000000)
      constant := (30657202123371210184302947861098212244135916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269763963669337050053/100000000000000000000)
  centralHi := (134881981834668525027/50000000000000000000)
  directionLo := (271195082272502096173/100000000000000000000)
  directionHi := (135597541136251048087/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree096.table
  base := (-89957339746093683471471984057423499343/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-628479062404481395226474310270000000000000)
      constant := (7408478253641224741630455623525959953030176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree096.table
  base := (-719658717972077805961814491744567225493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2585616947209171321175880130680000000000000)
      constant := (31382324396331579915808870172616259295213488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271195082272502096173/100000000000000000000)
  centralHi := (135597541136251048087/50000000000000000000)
  directionLo := (272618688286380986243/100000000000000000000)
  directionHi := (68154672071595246561/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree097.table
  base := (-2641423042841065619885901155634591565261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (13070439665070838070048964250000000000000)
      linear := (-635201002803660683376785206170000000000000)
      constant := (7582574784504934260616876475729905013302211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree097.table
  base := (-1320711521425526333648283600539614343739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1960000000000000000000000000000000000000000
      center := (2163)
      previous := (777)
      next := (0)
      square := (52281758660283352280195857000000000000000)
      linear := (-2613251591072463950238269369380000000000000)
      constant := (32115811257381527253758246746668971177254312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell001.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272618688286380986243/100000000000000000000)
  centralHi := (68154672071595246561/25000000000000000000)
  directionLo := (54806979758853613519/20000000000000000000)
  directionHi := (68508724698567016899/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree098.table
  base := (-479759452700290914861124287975025776213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (1867205666438691152864137750000000000000)
      linear := (-91703277600405710218156586010000000000000)
      constant := (1108380728270487285762564580612874097832545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 140
  table := BinomialMassData.Q37_140.Degree098.table
  base := (-599699315877236410734141997504873525399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 280000000000000000000000000000000000000000
      center := (309)
      previous := (111)
      next := (0)
      square := (7468822665754764611456551000000000000000)
      linear := (-377269462133679511328665515440000000000000)
      constant := (4693951813469095216399043969865454165155312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_140.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell001.Kernel098
