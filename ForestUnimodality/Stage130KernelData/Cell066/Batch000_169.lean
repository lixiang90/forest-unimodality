import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell066.Parameters
import ForestUnimodality.BinomialMassData.Q395_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q395_792.Batch050_099
import ForestUnimodality.BinomialMassData.Q395_792.Batch100_149
import ForestUnimodality.BinomialMassData.Q395_792.Batch150_199
import ForestUnimodality.BinomialMassData.Q1_2.Batch000_049
import ForestUnimodality.BinomialMassData.Q1_2.Batch050_099
import ForestUnimodality.BinomialMassData.Q1_2.Batch100_149
import ForestUnimodality.BinomialMassData.Q1_2.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree000.table
  base := (749313564407365579234010513/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (102754172432420118332707660000000000)
      constant := (29972542576294623169360420520000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree000.table
  base := (749313564407365579234010513/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (102754172432420118332707660000000000)
      constant := (29972542576294623169360420520000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree001.table
  base := (42307521708326740914470519669148937847541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-1342336001669375416077770182294200000000000)
      constant := (829645521404595827958437651780761823437498682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree001.table
  base := (8445039557593199851927224136867666357387/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-27461423705371976536349087940000000000)
      constant := (16896918782569634592958952368805332714774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6249980072154742059/12500000000000000000)
  directionHi := (49999840577237936473/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree002.table
  base := (62695317208240943199374272331841058449871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-13448537357794007900272173517333500000000000)
      constant := (2464601947153335049427545730351110605468742684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree002.table
  base := (124957561068012852282995270758857346946421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-1375640039579409329775772088500000000000)
      constant := (250601657728660003979399268716214693892842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6249980072154742059/12500000000000000000)
  centralHi := (49999840577237936473/100000000000000000000)
  directionLo := (70710452660822491221/100000000000000000000)
  directionHi := (35355226330411245611/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree003.table
  base := (157637694624984332337441041010444563493579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-2242821634137904302239499569244000000000000)
      constant := (173343225090468554406921337568071473394507531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree003.table
  base := (9808717136961072579947542690308955569773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-2064744486524519246142816978500000000000)
      constant := (158486105915537442836549057510193289116368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/100000000000000000000)
  centralHi := (35355226330411245611/50000000000000000000)
  directionLo := (86602264250120087683/100000000000000000000)
  directionHi := (21650566062530021921/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree004.table
  base := (52778811118913737524987954363361471760161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-26922252056688269540038818729058500000000000)
      constant := (1061399408362687654281013419508120319442675922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree004.table
  base := (105041799432290984652614545356676423393413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-2753848933469629162509861868500000000000)
      constant := (107793079511449803312166089533676423393413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86602264250120087683/100000000000000000000)
  centralHi := (21650566062530021921/25000000000000000000)
  directionLo := (19999936230895174589/20000000000000000000)
  directionHi := (49999840577237936473/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree005.table
  base := (37544753719293650919484336696628911609647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-33659109406135400359922141334921000000000000)
      constant := (777888509772036326242510154505631644122300494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree005.table
  base := (74717270136696918635975975284280536258769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-3442953380414739078876906758500000000000)
      constant := (79017750794326829355874211618030536258769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19999936230895174589/20000000000000000000)
  centralHi := (49999840577237936473/50000000000000000000)
  directionLo := (111803042394856349999/100000000000000000000)
  directionHi := (2236060847897127/2000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree006.table
  base := (56223608056075554753056860639723700351873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-4488440750620281242200607104531500000000000)
      constant := (67938983002494098818386514644624109683189697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree006.table
  base := (55952243439912254060025123582273080011963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-4132057827359848995243951648500000000000)
      constant := (62146476899485811798453574517773080011963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111803042394856349999/100000000000000000000)
  centralHi := (2236060847897127/2000000000000000)
  directionLo := (122474096634738464137/100000000000000000000)
  directionHi := (61237048317369232069/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree007.table
  base := (43778664016506754233197619176981457685069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-47132824105029661999688786546646000000000000)
      constant := (511304890130747858491739865911223860521361269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree007.table
  base := (8714996781099739237055734803823692654719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-964232454860991782322199307700000000000)
      constant := (10401504478097691180084172400273692654719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/100000000000000000000)
  centralHi := (61237048317369232069/50000000000000000000)
  directionLo := (13228714376024778641/10000000000000000000)
  directionHi := (132287143760247786411/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree008.table
  base := (7006924543624324005344098067281980583433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-10773936290895358563914421830501700000000000)
      constant := (90158280709419305572974138284659191698226833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree008.table
  base := (34875963688576037888353260279183933092131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-5510266721250068827978041428500000000000)
      constant := (45891359422454554538392707753183933092131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/10000000000000000000)
  centralHi := (132287143760247786411/100000000000000000000)
  directionLo := (70710452660822491221/50000000000000000000)
  directionHi := (141420905321644982443/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree009.table
  base := (14267547903078342141153044958627595149697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-748228874122517575795746071091000000000000)
      constant := (5131312654400693198445553380077096776226674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree009.table
  base := (55482293060144334923065952730553068633/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-6199371168195178744345086318500000000000)
      constant := (42349739253033728023729997208793171140096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/50000000000000000000)
  centralHi := (141420905321644982443/100000000000000000000)
  directionLo := (74999760865856904709/50000000000000000000)
  directionHi := (149999521731713809419/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree010.table
  base := (23478106773467586692681647136622834614823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-67343396153371054459338754364233500000000000)
      constant := (397979482762304846747816836556921652059880223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree010.table
  base := (4674283274039715090663174027618986119681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-1377695123028057732142426241700000000000)
      constant := (8117236654454454169540080786118986119681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999760865856904709/50000000000000000000)
  centralHi := (149999521731713809419/100000000000000000000)
  directionLo := (158113378869379970769/100000000000000000000)
  directionHi := (15811337886937997077/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree011.table
  base := (121280442963605359799214148114752697549/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (2430)
      previous := (1215)
      next := (1215)
      square := (11163492040510780645146127218000000000000)
      linear := (-122446700004658157486317482595200000000000)
      constant := (650122855405450480090293146338407742047008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree011.table
  base := (772563229999907878342512890757887930183/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-303103202483415943083167043940000000000)
      constant := (1605814462855112566495807315527887930183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158113378869379970769/100000000000000000000)
  centralHi := (15811337886937997077/10000000000000000000)
  directionLo := (165830710772285185631/100000000000000000000)
  directionHi := (5182209711633912051/3125000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree012.table
  base := (16040011903313342720602437546878352209099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-8979678983585035122122822175106500000000000)
      constant := (44330210788390216444997263674761775555708811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree012.table
  base := (7980814129588155362180018393169137179123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-8266684509030508493446220988500000000000)
      constant := (40753975223335404695823746677338274358246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165830710772285185631/100000000000000000000)
  centralHi := (5182209711633912051/3125000000000000000)
  directionLo := (86602264250120087683/50000000000000000000)
  directionHi := (173204528500240175367/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree013.table
  base := (3302217765378379034820587126045750543729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-87553968201712446918988722181821000000000000)
      constant := (413210360595386150959327873606764323066351716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree013.table
  base := (13140615691234015897877354211729300622509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-8955788955975618409813265878500000000000)
      constant := (42238581021644641595155935819479300622509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86602264250120087683/50000000000000000000)
  centralHi := (173204528500240175367/100000000000000000000)
  directionLo := (180276988966256368513/100000000000000000000)
  directionHi := (90138494483128184257/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree014.table
  base := (10794184822825344490632953365226199340937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-94290825551159577738872044787683500000000000)
      constant := (434890418202064270618197350683784479740523537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree014.table
  base := (5367240988169494965037738712657510528921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-9644893402920728326180310768500000000000)
      constant := (44482617896473702311352453194815021057842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180276988966256368513/100000000000000000000)
  centralHi := (90138494483128184257/50000000000000000000)
  directionLo := (93541136416670887189/50000000000000000000)
  directionHi := (187082272833341774379/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree015.table
  base := (1742593680969400045465507952503445146613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-2245059620013482412416785942078800000000000)
      constant := (10293305245849466559782993253114220514661557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree015.table
  base := (4330325027429338165736503755568311854559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-10333997849865838242547355658500000000000)
      constant := (47403508788190030354931899887386623709118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93541136416670887189/50000000000000000000)
  centralHi := (187082272833341774379/100000000000000000000)
  directionLo := (193648549868668365831/100000000000000000000)
  directionHi := (24206068733583545729/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree016.table
  base := (1725962683386115264311073240630298756037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-107764540250053839378638689999408500000000000)
      constant := (497533816282263872190354004522455232431674548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree016.table
  base := (3428996011357151255208020369459957793159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-11023102296810948158914400548500000000000)
      constant := (50940125792714853134240372166919915586318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193648549868668365831/100000000000000000000)
  centralHi := (24206068733583545729/12500000000000000000)
  directionLo := (199999362308951745891/100000000000000000000)
  directionHi := (49999840577237936473/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree017.table
  base := (1329970138502259316941035016931983555907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-114501397599500970198522012605271000000000000)
      constant := (537435489609817833745175741612233202075778028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree017.table
  base := (105594198687000653423071138809989922153/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-468488269750242323011257817540000000000)
      constant := (2201826838579693394141073994609979844306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199999362308951745891/100000000000000000000)
  centralHi := (49999840577237936473/25000000000000000000)
  directionLo := (206154623963995911857/100000000000000000000)
  directionHi := (103077311981997955929/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree018.table
  base := (1962124115183024958162739837687009434653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-1496768579616643222449448582853500000000000)
      constant := (7191888701292347549859921633469006283186026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree018.table
  base := (972274768712289115315857798823899527887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-12401311190701167991648490328500000000000)
      constant := (59683439588605765160369208061795598111548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206154623963995911857/100000000000000000000)
  centralHi := (103077311981997955929/50000000000000000000)
  directionLo := (212131357982467473663/100000000000000000000)
  directionHi := (828638117119013569/390625000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree019.table
  base := (1343800969143157858628996307724021957673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-127975112298395231838288657816996000000000000)
      constant := (632568624636600500187932938433442372164306146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree019.table
  base := (1328443233090957408196082716210616246219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-13090415637646277908015535218500000000000)
      constant := (64824158687025384990413948685671232492438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212131357982467473663/100000000000000000000)
  centralHi := (828638117119013569/390625000000000000)
  directionLo := (217944252269324542567/100000000000000000000)
  directionHi := (27243031533665567821/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree020.table
  base := (793133514092388252963268753239723681949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-134711969647842362658171980422858500000000000)
      constant := (687280373864995724621424579299798813613564298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree020.table
  base := (389865461379390453730250351884838797311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-13779520084591387824382580108500000000000)
      constant := (70444217996920448422042313492539355189244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217944252269324542567/100000000000000000000)
  centralHi := (27243031533665567821/12500000000000000000)
  directionLo := (111803042394856349999/50000000000000000000)
  directionHi := (223606084789712699999/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree021.table
  base := (120200114302644558351169494829705932697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-3143307266606433188401228956193800000000000)
      constant := (16588658501048107191600008539441143510707033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree021.table
  base := (577638037837781279684561416700121027841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-14468624531536497740749624998500000000000)
      constant := (76524430343272639278088924778450121027841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111803042394856349999/50000000000000000000)
  centralHi := (223606084789712699999/100000000000000000000)
  directionLo := (114564027090458672641/50000000000000000000)
  directionHi := (229128054180917345283/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree022.table
  base := (-283919822290616331161386833431319080881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-1224675077245757225602798558963500000000000)
      constant := (6694564508538900661494734003312063154448639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree022.table
  base := (-152128712485821497397823047537516708217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-15157728978481607657116669888500000000000)
      constant := (83049123257967741353075290988424966583566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114564027090458672641/50000000000000000000)
  centralHi := (229128054180917345283/100000000000000000000)
  directionLo := (11726002011606791019/5000000000000000000)
  directionHi := (234520040232135820381/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree023.table
  base := (-540693236151487352496495070150945769937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-154922541696183755117821948240446000000000000)
      constant := (877812035203856025990925019557189754767694926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree023.table
  base := (-1099071480196830809345389149200128582137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-15846833425426717573483714778500000000000)
      constant := (90005449803719634846175644101049871417863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11726002011606791019/5000000000000000000)
  centralHi := (234520040232135820381/100000000000000000000)
  directionLo := (239790811600928139233/100000000000000000000)
  directionHi := (119895405800464069617/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree024.table
  base := (-72079938455589757758676241239588080197/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 435600000000000000000000000000000000000000
      center := (6534)
      previous := (3267)
      next := (3267)
      square := (30017389708928987956948475408400000000000)
      linear := (-718486217980581715278690092650260000000000)
      constant := (4220866399768637145605061887431988580665467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree024.table
  base := (-1817361788923113239404059301100202365497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-16535937872371827489850759668500000000000)
      constant := (97382852319442988681950592560899797634503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239790811600928139233/100000000000000000000)
  centralHi := (119895405800464069617/50000000000000000000)
  directionLo := (122474096634738464137/50000000000000000000)
  directionHi := (9797927730779077131/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree025.table
  base := (-122724329344040069301598144440661725951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-33679251279015603351517718690434200000000000)
      constant := (205121089844167769512453612552175641445816996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree025.table
  base := (-616955351693141573404047587704686790431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-17225042319316937406217804558500000000000)
      constant := (105172637749515726851755602567931252838276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/50000000000000000000)
  centralHi := (9797927730779077131/4000000000000000000)
  directionLo := (62499800721547420591/25000000000000000000)
  directionHi := (49999840577237936473/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree026.table
  base := (-3046053878358919369026889787654714087129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-175133113744525147577471916058033500000000000)
      constant := (1105472966129601743711155050170112397232048671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree026.table
  base := (-3057619124906261723968845844485836998693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-17914146766262047322584849448500000000000)
      constant := (113367637302776777603603610576014163001307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62499800721547420591/25000000000000000000)
  centralHi := (49999840577237936473/20000000000000000000)
  directionLo := (254950162779864568717/100000000000000000000)
  directionHi := (127475081389932284359/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree027.table
  base := (-1791325355056911498229145470281027367127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-2245308285110768869103151094616000000000000)
      constant := (14681965074763190746522613074170585127155266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree027.table
  base := (-1796337210804613780699478563446476573417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-18603251213207157238951894338500000000000)
      constant := (121961931500941112906557685240357046853166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254950162779864568717/100000000000000000000)
  centralHi := (127475081389932284359/50000000000000000000)
  directionLo := (5196135855007205261/2000000000000000000)
  directionHi := (259806792750360263051/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree028.table
  base := (-508649788705772391387021115028317363293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-188606828443419409217238561269758500000000000)
      constant := (1276855831048754931911789094059045942178922456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree028.table
  base := (-2038940396893700949320130264740239810187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-19292355660152267155318939228500000000000)
      constant := (130950626847102794667884090229519520379626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5196135855007205261/2000000000000000000)
  centralHi := (259806792750360263051/100000000000000000000)
  directionLo := (13228714376024778641/5000000000000000000)
  directionHi := (264574287520495572821/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree029.table
  base := (-901954207787334011146959188574820004237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-39068737158573308007424376775124200000000000)
      constant := (273656602657327704197572138666513532888473163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree029.table
  base := (-1129321959726547972282398145283869128213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-19981460107097377071685984118500000000000)
      constant := (140329673743796415734145989014614523487148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/5000000000000000000)
  centralHi := (264574287520495572821/100000000000000000000)
  directionLo := (269257381838877480879/100000000000000000000)
  directionHi := (3365717272985968511/1250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree030.table
  base := (-490774546002837519994659250965352599653/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-4490678736495859352377893477366300000000000)
      constant := (32521947201886333249051270299924962037955766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree030.table
  base := (-2457125051759970293616391600311284005177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-20670564554042486988053029008500000000000)
      constant := (150095717644467633050977551676877431989646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269257381838877480879/100000000000000000000)
  centralHi := (3365717272985968511/1250000000000000000)
  directionLo := (136930202779076718501/50000000000000000000)
  directionHi := (273860405558153437003/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree031.table
  base := (-2632961243466353130660248563789400348669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-208817400491760801676888529087346000000000000)
      constant := (1562442211685268511522059318243968768115390262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree031.table
  base := (-1054309801674347871216204639175082368673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-4271933800197519380884014779700000000000)
      constant := (32049195425674671051049517481674917631327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136930202779076718501/50000000000000000000)
  centralHi := (273860405558153437003/100000000000000000000)
  directionLo := (27838733051312785487/10000000000000000000)
  directionHi := (278387330513127854871/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree032.table
  base := (-1396656911178614145269416930505806372749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-215554257841207932496771851693208500000000000)
      constant := (1665123983616629027394808588748020366962748204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree032.table
  base := (-5591492878867409903728322881443651914891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-22048773447932706820787118788500000000000)
      constant := (170778143870107760638902085894556348085109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27838733051312785487/10000000000000000000)
  centralHi := (278387330513127854871/100000000000000000000)
  directionLo := (70710452660822491221/25000000000000000000)
  directionHi := (56568362128657992977/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree033.table
  base := (-5871793470406434922520294247820866630237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1350)
      previous := (675)
      next := (675)
      square := (6201940022505989247303404010000000000000)
      linear := (-204124072718691518197112189439000000000000)
      constant := (1626734618074846634652369340001330950327867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree033.table
  base := (-58759991221627761921026757315711135573/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-909515115795112669486166547140000000000)
      constant := (7267612018500601009600522146447155457708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/25000000000000000000)
  centralHi := (56568362128657992977/20000000000000000000)
  directionLo := (57445443302571494987/20000000000000000000)
  directionHi := (35903402064107184367/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree034.table
  base := (-3061513658373825948422400781200857367427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-229027972540102194136538496904933500000000000)
      constant := (1881596504421710341746588025756584543883695946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree034.table
  base := (-6126661816742541717549466780428562311773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-23426982341822926653521208568500000000000)
      constant := (192980852827110445562235105674071437688227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57445443302571494987/20000000000000000000)
  centralHi := (35903402064107184367/12500000000000000000)
  directionLo := (291546665155808487749/100000000000000000000)
  directionHi := (1166186660623233951/400000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree035.table
  base := (-6341667204918930687174482163018603640887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-235764829889549324956421819510796000000000000)
      constant := (1995358385685642849207490642467850759465666513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree035.table
  base := (-1268961472788735532416210969960593467851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-4823217357753607313977650691700000000000)
      constant := (40929694912511410084711176622289406532149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291546665155808487749/100000000000000000000)
  centralHi := (1166186660623233951/400000000000000000)
  directionLo := (59160609199440238439/20000000000000000000)
  directionHi := (73950761499300298049/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree036.table
  base := (-1305765575915669397428688326055288559127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242000000000000000000000000000000000000000
      center := (3630)
      previous := (1815)
      next := (1815)
      square := (16676327616071659976082486338000000000000)
      linear := (-598769598120978903151370721275700000000000)
      constant := (5216762264846695574434148623703060084345633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree036.table
  base := (-6531540356664829573276496228057310698501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-24805191235713146486255298348500000000000)
      constant := (216692061075956194276396329684942689301499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59160609199440238439/20000000000000000000)
  centralHi := (73950761499300298049/25000000000000000000)
  directionLo := (299999043463427618837/100000000000000000000)
  directionHi := (149999521731713809419/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree037.table
  base := (-208919963189415345184213211489077853043/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-249238544588443586596188464722521000000000000)
      constant := (2233878389306948757229754733535389253544417824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree037.table
  base := (-6687781422024757782306027149303254407341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-25494295682658256402622343238500000000000)
      constant := (229110691740189116789586209160446745592659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299999043463427618837/100000000000000000000)
  centralHi := (149999521731713809419/50000000000000000000)
  directionLo := (304137156784107427779/100000000000000000000)
  directionHi := (15206857839205371389/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree038.table
  base := (-3406137827920005267052361901224145176691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-255975401937890717416071787328383500000000000)
      constant := (2358619799932102498538967826548959306246503018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree038.table
  base := (-340714923609836444707224168096540790517/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-5236680025920673263797877625700000000000)
      constant := (48380719728616510271630137157913836837932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304137156784107427779/100000000000000000000)
  centralHi := (15206857839205371389/5000000000000000000)
  directionLo := (61643943480108393223/20000000000000000000)
  directionHi := (77054929350135491529/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree039.table
  base := (-6909986117094136496052513117169145957277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-29190251031926427581772789992694000000000000)
      constant := (276334066741786263078720820235952643802525347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree039.table
  base := (-6911732535865962095760386933017090226323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-26872504576548476235356433018500000000000)
      constant := (255070140755951278795121237505232909773677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61643943480108393223/20000000000000000000)
  centralHi := (77054929350135491529/25000000000000000000)
  directionLo := (312248904325089924421/100000000000000000000)
  directionHi := (156124452162544962211/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree040.table
  base := (-697911155070326818450940268809366663193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-53889823327356995811167686508021700000000000)
      constant := (523806697163541082492380550335941294668090814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree040.table
  base := (-3490309564931016555250343255758738983163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-27561609023493586151723477908500000000000)
      constant := (268609782561965723377150915658482522033674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312248904325089924421/100000000000000000000)
  centralHi := (156124452162544962211/50000000000000000000)
  directionLo := (158113378869379970769/50000000000000000000)
  directionHi := (316226757738759941539/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree041.table
  base := (-1404020943755908823971968242519037471931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-55237194797246421975144351029194200000000000)
      constant := (550939203567105712632185190706880257487604269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree041.table
  base := (-1404281191421685802879598333352030003111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-5650142694087739213618104559700000000000)
      constant := (56504415271640479605641422135997969996889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158113378869379970769/50000000000000000000)
  centralHi := (316226757738759941539/100000000000000000000)
  directionLo := (20009699441743166679/6250000000000000000)
  directionHi := (64031038213578133373/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree042.table
  base := (-1758336141885850947249011194668559412189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-31435870148408804521733897527981500000000000)
      constant := (321554498075293254710502930867685005200504716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree042.table
  base := (-3517233787801013008980740830611058318951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-28939817917383805984457567688500000000000)
      constant := (296806647586664426537780643307277883362098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20009699441743166679/6250000000000000000)
  centralHi := (64031038213578133373/20000000000000000000)
  directionLo := (64807200348562130771/20000000000000000000)
  directionHi := (10126125054462832933/3125000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree043.table
  base := (-7019148482911237270359218943449846720963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-289659688685126371515488400357696000000000000)
      constant := (3036913769644671061003901768838674146037841637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree043.table
  base := (-3510058783829455232476029591181771027361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-29628922364328915900824612578500000000000)
      constant := (311463182665035722562110610852886457945278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64807200348562130771/20000000000000000000)
  centralHi := (10126125054462832933/3125000000000000000)
  directionLo := (327870880810138426613/100000000000000000000)
  directionHi := (163935440405069213307/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree044.table
  base := (-6977782470772696270642735644694651198563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-2449558231690690101945220850938500000000000)
      constant := (26309613814982639608361573456700983252916397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree044.table
  base := (-6978618644280615978002808841541496164237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-30318026811274025817191657468500000000000)
      constant := (326491418882314752478563928705458503835763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327870880810138426613/100000000000000000000)
  centralHi := (163935440405069213307/50000000000000000000)
  directionLo := (331661421544570371263/100000000000000000000)
  directionHi := (5182209711633912051/1562500000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree045.table
  base := (-1727367405169288883205905427486836847719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-3742387696099020162410556118141000000000000)
      constant := (41156009902242603276075980199245589715704004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree045.table
  base := (-3455095521139313573294201671211068775721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-31007131258219135733558702358500000000000)
      constant := (341891136001690031697665924161327862448558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331661421544570371263/100000000000000000000)
  centralHi := (5182209711633912051/1562500000000000000)
  directionLo := (167704563592284524999/50000000000000000000)
  directionHi := (335409127184569049999/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree046.table
  base := (-6814397148354348418708550024814298777971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-309870260733467763975138368175283500000000000)
      constant := (3487432526149558362576046591521067557677106229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree046.table
  base := (-6815019508563555419522460653758877159439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-31696235705164245649925747248500000000000)
      constant := (357662149276250948770602979251741122840561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167704563592284524999/50000000000000000000)
  centralHi := (335409127184569049999/100000000000000000000)
  directionLo := (1324669601165954183/390625000000000000)
  directionHi := (339115417898484270849/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree047.table
  base := (-6692722260592099707444803814305494769203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-316607118082914894795021690781146000000000000)
      constant := (3644848903032894413593004451519020439517041397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree047.table
  base := (-267730364567127408216825921170250942503/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-1295413606084374222651711685540000000000)
      constant := (14952172145398188771550377068919749057497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1324669601165954183/390625000000000000)
  centralHi := (339115417898484270849/100000000000000000000)
  directionLo := (171390818536330028393/50000000000000000000)
  directionHi := (342781637072660056787/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree048.table
  base := (-3272288521697534495590910162596375684087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-35927108381373558401656112598556500000000000)
      constant := (422876070906303038861152371297460093760058514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree048.table
  base := (-3272520049067446162725512091206903825207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-33074444599054465482659837028500000000000)
      constant := (390317468838788967430967207861586192349586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171390818536330028393/50000000000000000000)
  centralHi := (342781637072660056787/100000000000000000000)
  directionLo := (346409057000480350733/100000000000000000000)
  directionHi := (173204528500240175367/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree049.table
  base := (-6370072539353208471769567424974062988547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-330080832781809156434788335992871000000000000)
      constant := (3970538643192633049517815726926080927399250853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree049.table
  base := (-1274094381240798804831367721100911595227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-6752709809199915079805376383700000000000)
      constant := (81440307088396675190536614635049088404773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346409057000480350733/100000000000000000000)
  centralHi := (173204528500240175367/50000000000000000000)
  directionLo := (34999888404066555531/10000000000000000000)
  directionHi := (349998884040665555311/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree050.table
  base := (-77116276892172772625271385738357826497/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-67363538026251257450934331719746700000000000)
      constant := (827762000539743405943140573858997429080046448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree050.table
  base := (-6169646561103998198407123594072675584519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-34452653492944685315393926808500000000000)
      constant := (424456411421819436957037990368427324415481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34999888404066555531/10000000000000000000)
  centralHi := (349998884040665555311/100000000000000000000)
  directionLo := (176776131652056228053/50000000000000000000)
  directionHi := (353552263304112456107/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree051.table
  base := (-5942344486249445573992956674239224448851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-38172727497855935341617220133844000000000000)
      constant := (478966438472200626604503177202170828325201261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree051.table
  base := (-5942641476938325312112711700438023341831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-35141757939889795231760971698500000000000)
      constant := (442082019364193729980121126888811976658169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176776131652056228053/50000000000000000000)
  centralHi := (353552263304112456107/100000000000000000000)
  directionLo := (71414056584179468521/20000000000000000000)
  directionHi := (178535141460448671303/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree052.table
  base := (-5689265732025969734106590971158663684539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-350291404830150548894438303810458500000000000)
      constant := (4486201825136861111092174276427037687227833261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree052.table
  base := (-5689521811285454115938258890897546394431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-35830862386834905148128016588500000000000)
      constant := (460078294111527776271267826770102453605569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71414056584179468521/20000000000000000000)
  centralHi := (178535141460448671303/50000000000000000000)
  directionLo := (360553977932512737027/100000000000000000000)
  directionHi := (90138494483128184257/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree053.table
  base := (-5410121647051133114618833644268236787351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-357028262179597679714321626416321000000000000)
      constant := (4665321092872317256454104702932068729997172849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree053.table
  base := (-216413697293187078977920739631711619923/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-1460798673351200602579802459140000000000)
      constant := (19137807231825491338636553467478288380077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360553977932512737027/100000000000000000000)
  centralHi := (90138494483128184257/25000000000000000000)
  directionLo := (45500541731099904807/12500000000000000000)
  directionHi := (364004333848799238457/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree054.table
  base := (-1276239806327457186253429268088211568661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-4490927401593145809064258629903500000000000)
      constant := (59852534430470717764745023123335305600768076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree054.table
  base := (-638143695650575421216335607626285700953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-37209071280725124980862106368500000000000)
      constant := (497182633191388642081970462278489714392376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45500541731099904807/12500000000000000000)
  centralHi := (364004333848799238457/100000000000000000000)
  directionLo := (367422289904215392411/100000000000000000000)
  directionHi := (91855572476053848103/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree055.table
  base := (-477381809168839918986767257375876964169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (2430)
      previous := (1215)
      next := (1215)
      square := (11163492040510780645146127218000000000000)
      linear := (-612399961782631308023286399385200000000000)
      constant := (8321328966546748289400805261570576681804622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree055.table
  base := (-238699108540507716799838648533969628667/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-7579635145534046979445830251700000000000)
      constant := (103258122467576386217045437715114121485332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367422289904215392411/100000000000000000000)
  centralHi := (91855572476053848103/25000000000000000000)
  directionLo := (185404371021968161647/50000000000000000000)
  directionHi := (74161748408787264659/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree056.table
  base := (-552091458968153307564464295635296751929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-377238834227939072173971594233908500000000000)
      constant := (5224366972946383282790431159375325152274750968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree056.table
  base := (-883374620269243184831233469169315073739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-7717456034923068962719239229700000000000)
      constant := (107153817076583452884954826210430684926261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185404371021968161647/50000000000000000000)
  centralHi := (74161748408787264659/20000000000000000000)
  directionLo := (374164545666683548757/100000000000000000000)
  directionHi := (187082272833341774379/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree057.table
  base := (-4033728173063587790469725172074625757981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-42663965730820689221539435204419000000000000)
      constant := (601993761884711793543058759863383701299558691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree057.table
  base := (-2016925034673434665265094049063059217889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-39276384621560454729963241038500000000000)
      constant := (555618024613960560904289969596623881564222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374164545666683548757/100000000000000000000)
  centralHi := (187082272833341774379/50000000000000000000)
  directionLo := (37749051814807869167/10000000000000000000)
  directionHi := (377490518148078691671/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree058.table
  base := (-724966281809934716179116293893728632341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-78142509785366666762747647889126700000000000)
      constant := (1123026888682731444051390693221344815674425859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree058.table
  base := (-453117057602912806236892022764157671731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-39965489068505564646330285928500000000000)
      constant := (575837406645000632628998403254386738626152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37749051814807869167/10000000000000000000)
  centralHi := (377490518148078691671/100000000000000000000)
  directionLo := (95196860291402907083/25000000000000000000)
  directionHi := (380787441165611628333/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree059.table
  base := (-3190061490888000292175148005204836881277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-397449406276280464633621562051496000000000000)
      constant := (5815938535190417072070502384989573487476604123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree059.table
  base := (-3190152018005706798173151418245137382749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-40654593515450674562697330818500000000000)
      constant := (596427211733807288082977292205004862617251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95196860291402907083/25000000000000000000)
  centralHi := (380787441165611628333/100000000000000000000)
  directionLo := (192028031421979735529/50000000000000000000)
  directionHi := (384056062843959471059/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree060.table
  base := (-2729435409092746302150214111171554500161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-44909584847303066161500542739706500000000000)
      constant := (668928440640961803894105357575240427149324671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree060.table
  base := (-2729513412929645472078191518640703846789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-41343697962395784479064375708500000000000)
      constant := (617387423208344964169512678736359296153211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192028031421979735529/50000000000000000000)
  centralHi := (384056062843959471059/100000000000000000000)
  directionLo := (193648549868668365831/50000000000000000000)
  directionHi := (387297099737336731663/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree061.table
  base := (-11214837612721865666575137103432763293/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3920400000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (270156507380360891612536278675600000000000)
      linear := (-16436924839006989050935528290528840000000000)
      constant := (249135463776679492232172993784613912645722456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree061.table
  base := (-2243034729588532587396125446359178373603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-42032802409340894395431420598500000000000)
      constant := (638718026984620246772818693885390821626397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193648549868668365831/50000000000000000000)
  centralHi := (387297099737336731663/100000000000000000000)
  directionLo := (3905112386637569809/1000000000000000000)
  directionHi := (390511238663756980901/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree062.table
  base := (-865334984975442223298416624846954877137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-417659978324621857093271529869083500000000000)
      constant := (6440030302163933140461884332962557490498360526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree062.table
  base := (-21634098368074960354525629797698716581/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-8544381371257200862359693097700000000000)
      constant := (132083802232233901441732048093936820534704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3905112386637569809/1000000000000000000)
  centralHi := (390511238663756980901/100000000000000000000)
  directionLo := (19684956920225338303/5000000000000000000)
  directionHi := (393699138404506766061/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree063.table
  base := (-1192553016218984148983559156089464813933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-5239467107087271455717961141666000000000000)
      constant := (82164036893865964617620222286714268507514107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree063.table
  base := (-1192602892667134971631949445412314117959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-43411011303231114228165510378500000000000)
      constant := (682490365677827648700381335374837685882041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19684956920225338303/5000000000000000000)
  centralHi := (393699138404506766061/100000000000000000000)
  directionLo := (39686143128074335923/10000000000000000000)
  directionHi := (396861431280743359231/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree064.table
  base := (-125725068835428752615586336043539025749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-86226738604703223746607635016161700000000000)
      constant := (1374831313606843087421471307715465274008634051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree064.table
  base := (-628668305401246521960432003359322789629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-44100115750176224144532555268500000000000)
      constant := (704932082028445371743227369228640677210371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39686143128074335923/10000000000000000000)
  centralHi := (396861431280743359231/100000000000000000000)
  directionLo := (399998724617903491783/100000000000000000000)
  directionHi := (49999840577237936473/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree065.table
  base := (-607723443593729537328411695903409679/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-437870550372963249552921497686671000000000000)
      constant := (7096638969053470058132049562196142562381111744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree065.table
  base := (-19465650880349000386708979161608531887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-44789220197121334060899600158500000000000)
      constant := (727744153018910309815772422130426782936226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399998724617903491783/100000000000000000000)
  centralHi := (49999840577237936473/12500000000000000000)
  directionLo := (403111602107528780791/100000000000000000000)
  directionHi := (50388950263441097599/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree066.table
  base := (576633897616378375200450133402610065423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1350)
      previous := (675)
      next := (675)
      square := (6201940022505989247303404010000000000000)
      linear := (-408271265126180330920849238101500000000000)
      constant := (6724273765402143212698413620234373490588807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree066.table
  base := (576602032266577571673236811639365179833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-45478324644066443977266645048500000000000)
      constant := (750926572563234529897760638202139365179833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403111602107528780791/100000000000000000000)
  centralHi := (50388950263441097599/12500000000000000000)
  directionLo := (101550156268789110197/25000000000000000000)
  directionHi := (406200625075156440789/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree067.table
  base := (608976993291906186492126083695323319413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-451344265071857511192688142898396000000000000)
      constant := (7552442000857413764826943471410511821457133626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree067.table
  base := (608963273453712602375268799324329713111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-46167429091011553893633689938500000000000)
      constant := (774479335511644876998563022735898659426222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101550156268789110197/25000000000000000000)
  centralHi := (406200625075156440789/100000000000000000000)
  directionLo := (102316583415518785561/25000000000000000000)
  directionHi := (81853266732415028449/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree068.table
  base := (942530755030627431789556314296321212537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-458081122421304642012571465504258500000000000)
      constant := (7785762536379232750972767199623485238408150274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree068.table
  base := (1885037883613353053880339075810938759601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-46856533537956663810000734828500000000000)
      constant := (798402437505592859273601430404810938759601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102316583415518785561/25000000000000000000)
  centralHi := (81853266732415028449/20000000000000000000)
  directionLo := (206154623963995911857/50000000000000000000)
  directionHi := (82461849585598364743/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree069.table
  base := (2577952693936546821285406215410622143261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-51646442196750196981383865345569000000000000)
      constant := (891410633344257516272795732165910136264011229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree069.table
  base := (2577932352725703548111141123560029611743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-47545637984901773726367779718500000000000)
      constant := (822695874855419819151924361089310029611743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206154623963995911857/50000000000000000000)
  centralHi := (82461849585598364743/20000000000000000000)
  directionLo := (16613194755239363737/4000000000000000000)
  directionHi := (207664934440492046713/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree070.table
  base := (1648312170667715487767932250733093918061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-471554837120198903652338110715983500000000000)
      constant := (8263241460682103855765296843172695106981831722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree070.table
  base := (412075853777092320028772988929629764923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-48234742431846883642734824608500000000000)
      constant := (847359644437098018506319054958937038119384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16613194755239363737/4000000000000000000)
  centralHi := (207664934440492046713/50000000000000000000)
  directionLo := (418328679440514391927/100000000000000000000)
  directionHi := (52291084930064298991/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree071.table
  base := (2020536871920929799863055346597683395049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-478291694469646034472221433321846000000000000)
      constant := (8507399791585405695134723463708276383659750498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree071.table
  base := (252566166906273098928833192328423721779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-48923846878791993559101869498500000000000)
      constant := (872393743605041368829409375651504779548464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418328679440514391927/100000000000000000000)
  centralHi := (52291084930064298991/12500000000000000000)
  directionLo := (210653072669373765397/50000000000000000000)
  directionHi := (84261229067749506159/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree072.table
  base := (4811298606478931656151474063806874846139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-5988006812581397102371663653428500000000000)
      constant := (108088526794014253796208616954403131856382819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree072.table
  base := (1202821408196540849359205922034279772281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-49612951325737103475468914388500000000000)
      constant := (897798170118459436902627564234137119089124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210653072669373765397/50000000000000000000)
  centralHi := (84261229067749506159/20000000000000000000)
  directionLo := (424262715964934947327/100000000000000000000)
  directionHi := (828638117119013569/195312500000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree073.table
  base := (5607296984296578341574054826502367434681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-491765409168540296111988078533571000000000000)
      constant := (9006554077808894818499285716157416421977308481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree073.table
  base := (1401821454713094453899561368932786133567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-50302055772682213391835959278500000000000)
      constant := (923572922079130480537615204438481144534268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424262715964934947327/100000000000000000000)
  centralHi := (828638117119013569/195312500000000000)
  directionLo := (13349963286162512461/3125000000000000000)
  directionHi := (427198825157200398753/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree074.table
  base := (6429067228753319643243914207654099685803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-498502266517987426931871401139433500000000000)
      constant := (9261549997909271432548924542340239081020555203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree074.table
  base := (6429057620450955034542214822605828894797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-50991160219627323308203004168500000000000)
      constant := (949717997878806441931568914647105828894797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13349963286162512461/3125000000000000000)
  centralHi := (427198825157200398753/100000000000000000000)
  directionLo := (430114891945677097783/100000000000000000000)
  directionHi := (53764361493209637223/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree075.table
  base := (1455321588473157999130909767957363818199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-11227536085942990172261216083228800000000000)
      constant := (211559075931545554082984115830011037948018711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree075.table
  base := (7276599674840291047943368358569959020263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-51680264666572433224570049058500000000000)
      constant := (976233396154745717078163331489819959020263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430114891945677097783/100000000000000000000)
  centralHi := (53764361493209637223/12500000000000000000)
  directionLo := (433011321250600438417/100000000000000000000)
  directionHi := (216505660625300219209/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree076.table
  base := (4074958970170117663313264422491944165657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-511975981216881688571638046351158500000000000)
      constant := (9782379323227566738393937133954728339535208514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree076.table
  base := (4074955413589545915402185202144634458323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-52369369113517543140937093948500000000000)
      constant := (1003119115752107011952401119287289268916646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433011321250600438417/100000000000000000000)
  centralHi := (216505660625300219209/50000000000000000000)
  directionLo := (87177700907729817027/20000000000000000000)
  directionHi := (27243031533665567821/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree077.table
  base := (9048996218102283089988610933443990781443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-4286882963358089416458854288901000000000000)
      constant := (83043080223037094390106247534459432003296883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree077.table
  base := (4524495049357061687750734455823567011367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-53058473560462653057304138838500000000000)
      constant := (1030375155692137092546658525991397134022734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87177700907729817027/20000000000000000000)
  centralHi := (27243031533665567821/6250000000000000000)
  directionLo := (219373410220273227941/50000000000000000000)
  directionHi := (438746820440546455883/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree078.table
  base := (9973841923811210260182417676982885778707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-58383299546197327801267187951431500000000000)
      constant := (1146406506650047117309727112035716862613011923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree078.table
  base := (9973836659862336822630853255580920071427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-53747578007407762973671183728500000000000)
      constant := (1058001515145252910001531740977080920071427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219373410220273227941/50000000000000000000)
  centralHi := (438746820440546455883/100000000000000000000)
  directionLo := (55198329416585143523/12500000000000000000)
  directionHi := (88317327066536229637/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree079.table
  base := (2184890867017576476482429832452885365743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-106437310653044616206257602833749200000000000)
      constant := (2118143374947267149071309533791940448219647143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree079.table
  base := (2731112451857213677506966513132732728571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-54436682454352872890038228618500000000000)
      constant := (1085998193408259586854856106860780930914284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55198329416585143523/12500000000000000000)
  centralHi := (88317327066536229637/20000000000000000000)
  directionLo := (27775518992829729777/6250000000000000000)
  directionHi := (444408303885275676433/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree080.table
  base := (238016656786117101566770283004735809241/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3920400000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (270156507380360891612536278675600000000000)
      linear := (-21556936424586808474046853470984340000000000)
      constant := (434695505825634868342310541606015831332742082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree080.table
  base := (1487603618165117969075461472353905365143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-55125786901297982806405273508500000000000)
      constant := (1114365189885064389821542808118831242921144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27775518992829729777/6250000000000000000)
  centralHi := (444408303885275676433/100000000000000000000)
  directionLo := (447212169579425399997/100000000000000000000)
  directionHi := (223606084789712699999/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree081.table
  base := (12902976916896451465027116183037986029803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-6736546518075522749025366165191000000000000)
      constant := (137625566265083201768661130891481815059606163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree081.table
  base := (12902973568217971249235070586259342052133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-55814891348243092722772318398500000000000)
      constant := (1143102504070346686200468584903009342052133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447212169579425399997/100000000000000000000)
  centralHi := (223606084789712699999/50000000000000000000)
  directionLo := (14062455162348169633/3125000000000000000)
  directionHi := (449998565195141428257/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree082.table
  base := (3482721531800998814141811043712478922077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-552397125313564473490937981986333500000000000)
      constant := (11431566535910072366189700975786492773661106708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree082.table
  base := (696544162387072782645244739847238857577/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-11300799159037640527827872657700000000000)
      constant := (234442027107145598888923265907088955430308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14062455162348169633/3125000000000000000)
  centralHi := (449998565195141428257/100000000000000000000)
  directionLo := (7074497082380633757/1562500000000000000)
  directionHi := (452767813272360560449/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree083.table
  base := (7492280048249667957520417359401370312599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-559133982663011604310821304592196000000000000)
      constant := (11719074647292951372920076721429061754617565598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree083.table
  base := (14984557620740196222840632845251738676403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-57193100242133312555506408178500000000000)
      constant := (1201688083918057113813213510450501738676403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7074497082380633757/1562500000000000000)
  centralHi := (452767813272360560449/100000000000000000000)
  directionLo := (14235007079585317519/3125000000000000000)
  directionHi := (455520226546730160609/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree084.table
  base := (16063998507820482533240205778340251876271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-62874537779162081681189403022006500000000000)
      constant := (1334466133168203543396792927499716284293259119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree084.table
  base := (2007999547420651528143131233824140146761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-57882204689078422471873453068500000000000)
      constant := (1231536348909485063572362892787593121174088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14235007079585317519/3125000000000000000)
  centralHi := (455520226546730160609/100000000000000000000)
  directionLo := (114564027090458672641/25000000000000000000)
  directionHi := (91651221672366938113/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree085.table
  base := (17169201092360356048731838009496757201471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-572607697361905865950587949803921000000000000)
      constant := (12304928186938135737251968930901439436081617271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree085.table
  base := (17169199262659607681639825376511259298867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-58571309136023532388240497958500000000000)
      constant := (1261754930249054947743886156050261259298867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114564027090458672641/25000000000000000000)
  centralHi := (91651221672366938113/20000000000000000000)
  directionLo := (230487876529701008193/50000000000000000000)
  directionHi := (460975753059402016387/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree086.table
  base := (18300167622164875848119100038783192807653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-579344554711352996770471272409783500000000000)
      constant := (12603273610331684968870674087549474072707807053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree086.table
  base := (2287520756178873348383953751880243316663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-59260413582968642304607542848500000000000)
      constant := (1292343827715574370522529970890541946533304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230487876529701008193/50000000000000000000)
  centralHi := (460975753059402016387/100000000000000000000)
  directionLo := (46367944634891031229/10000000000000000000)
  directionHi := (463679446348910312291/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree087.table
  base := (19456897903941076949049436078885914935281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-65120156895644458621150510557294000000000000)
      constant := (1433914607422223915070579379796676605114521009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree087.table
  base := (19456896552209922967190394176114402812449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-59949518029913752220974587738500000000000)
      constant := (1323303041121573905334044267698364402812449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46367944634891031229/10000000000000000000)
  centralHi := (463679446348910312291/100000000000000000000)
  directionLo := (466367465657909295373/100000000000000000000)
  directionHi := (233183732828954647687/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree088.table
  base := (10319695886902883165112173929430359333353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-4899324540580555854630065434888500000000000)
      constant := (109180179791214110435899531745535218212003186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree088.table
  base := (4127878122425655354767273209829065082623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-12127724495371772427468326525700000000000)
      constant := (270926514061637082546053858932629065082623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466367465657909295373/100000000000000000000)
  centralHi := (233183732828954647687/50000000000000000000)
  directionLo := (11726002011606791019/2500000000000000000)
  directionHi := (469040080464271640761/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree089.table
  base := (341369517075488459478779979504247954789/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-599555126759694389230121240227371000000000000)
      constant := (13519984472780731133180957071185529307862767296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree089.table
  base := (546191202364418575357227662832836220611/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-12265545384760794410741735503700000000000)
      constant := (277266483028159917503696922532812689764888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11726002011606791019/2500000000000000000)
  centralHi := (469040080464271640761/100000000000000000000)
  directionLo := (235848776305750431451/50000000000000000000)
  directionHi := (471697552611500862903/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree090.table
  base := (23081669743266758445674928626639776284327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-7485086223569648395679068676953500000000000)
      constant := (170775057034289023698309583030379662930403567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree090.table
  base := (23081668885522624356018519120420239671227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-62016831370749081970075722408500000000000)
      constant := (1418402575505383732366160125252920239671227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235848776305750431451/50000000000000000000)
  centralHi := (471697552611500862903/100000000000000000000)
  directionLo := (118585034152034978077/25000000000000000000)
  directionHi := (474340136608139912309/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree091.table
  base := (12170726812666241790595017659694148771979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-613028841458588650869887885439096000000000000)
      constant := (14149187194749005158228227915618230797978332358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree091.table
  base := (12170726444193549239950425273608082459159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-62705935817694191886442767298500000000000)
      constant := (1450843051305359024954172079106466164918318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118585034152034978077/25000000000000000000)
  centralHi := (474340136608139912309/100000000000000000000)
  directionLo := (476968079912249518929/100000000000000000000)
  directionHi := (47696807991224951893/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree092.table
  base := (25627000654499514144995188756654033750893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-619765698808035781689771208044958500000000000)
      constant := (14469207196867045878105461859511292434792502293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree092.table
  base := (25627000021396691602023098297216147821271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-63395040264639301802809812188500000000000)
      constant := (1483653842458951991498607471728216147821271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476968079912249518929/100000000000000000000)
  centralHi := (47696807991224951893/10000000000000000000)
  directionLo := (479581623201856278467/100000000000000000000)
  directionHi := (119895405800464069617/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree093.table
  base := (13469155379590734920303563996872711186837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-69611395128609212501072725627869000000000000)
      constant := (1643648847269990551767660624069001733714930986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree093.table
  base := (13469155107668366580579332214117565057101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-64084144711584411719176857078500000000000)
      constant := (1516834948896947961438239705175985130114202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479581623201856278467/100000000000000000000)
  centralHi := (119895405800464069617/25000000000000000000)
  directionLo := (3767039067439117627/781250000000000000)
  directionHi := (482181000632207056257/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree094.table
  base := (14137691939387769071348277182367739729981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-633239413506930043329537853256683500000000000)
      constant := (15120084479843644256077926730722649934187087562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree094.table
  base := (14137691705822807802311178667521340086659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-64773249158529521635543901968500000000000)
      constant := (1550386370560785327220383587844542680173318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3767039067439117627/781250000000000000)
  centralHi := (482181000632207056257/100000000000000000000)
  directionLo := (96953288016121592667/20000000000000000000)
  directionHi := (60595805010075995417/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree095.table
  base := (7409554990499958370631309594469614770979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-639976270856377174149421175862546000000000000)
      constant := (15450941759605619988153201814567595371231460716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree095.table
  base := (1852388722549877007361723043059698304789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-65462353605474631551910946858500000000000)
      constant := (1584308107400938782030412511405205172876624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96953288016121592667/20000000000000000000)
  centralHi := (60595805010075995417/12500000000000000000)
  directionLo := (487338163379572480731/100000000000000000000)
  directionHi := (121834540844893120183/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree096.table
  base := (31026818965482162878506234856425292693853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-71857014245091589441033833163156500000000000)
      constant := (1753934607143416810969137468719837143743605917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree096.table
  base := (15513409310466638710274151961220501082987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-66151458052419741468277991748500000000000)
      constant := (1618600159375547620588220481290441002165974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487338163379572480731/100000000000000000000)
  centralHi := (121834540844893120183/25000000000000000000)
  directionLo := (122474096634738464137/25000000000000000000)
  directionHi := (489896386538953856549/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree097.table
  base := (8110295213140526875064224497941440994901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-653449985555271435789187821074271000000000000)
      constant := (16123493593539729422828452630885277971514098804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree097.table
  base := (32441180556691394737867239369284635246689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-66840562499364851384645036638500000000000)
      constant := (1653262526449251886118770173834034635246689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/25000000000000000000)
  centralHi := (489896386538953856549/100000000000000000000)
  directionLo := (98488263991538260567/20000000000000000000)
  directionHi := (123110329989422825709/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree098.table
  base := (33881305592274120831526761434848212892689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-660186842904718566609071143680133500000000000)
      constant := (16465188147049061039066077231100771084561244889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree098.table
  base := (6776261067645124672542549800276343617161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-13505933389261992260202416305700000000000)
      constant := (337659041718440963583005992601576343617161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98488263991538260567/20000000000000000000)
  centralHi := (123110329989422825709/25000000000000000000)
  directionLo := (123743292156439359637/25000000000000000000)
  directionHi := (494973168625757438549/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree099.table
  base := (883679828962106264848722515835888975509/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-13609299056303758747657473039200000000000)
      constant := (343036325366036267343226952180155861804072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree099.table
  base := (35347192940364404251944399174350969175177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-68218771393255071217379126418500000000000)
      constant := (1723698205779234856933859415167600969175177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123743292156439359637/25000000000000000000)
  centralHi := (494973168625757438549/100000000000000000000)
  directionLo := (248746066158427778447/50000000000000000000)
  directionHi := (99498426463371111379/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree100.table
  base := (4604855441144656174484774322410615416383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-673660557603612828248837788891858500000000000)
      constant := (17159414525864400689409217481346790283567758264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree100.table
  base := (4604855417737533697455407882137160141283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-68907875840200181133746171308500000000000)
      constant := (1759471517989134535349339603482097281130264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248746066158427778447/50000000000000000000)
  centralHi := (99498426463371111379/20000000000000000000)
  directionLo := (499998405772379364729/100000000000000000000)
  directionHi := (49999840577237936473/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree101.table
  base := (38356256685734363097248980218752905264223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-680397414953059959068721111497721000000000000)
      constant := (17511946350772546914502435736786768943244649623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree101.table
  base := (19178128262493194552704089396966412157999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-69596980287145291050113216198500000000000)
      constant := (1795615145204057022921069366095682824315998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499998405772379364729/100000000000000000000)
  centralHi := (49999840577237936473/10000000000000000000)
  directionLo := (251246089438557299757/50000000000000000000)
  directionHi := (100498435775422919903/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree102.table
  base := (39899432612605073279381786319722119799131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-76348252478056343320956048233731500000000000)
      constant := (1985343399903783029490334895595832388461253659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree102.table
  base := (39899432474624467076003516661937435015817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-70286084734090400966480261088500000000000)
      constant := (1832129087409004023895813073285437435015817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251246089438557299757/50000000000000000000)
  centralHi := (100498435775422919903/20000000000000000000)
  directionLo := (252486818413565574877/50000000000000000000)
  directionHi := (100994727365426229951/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree103.table
  base := (20734185648329301563733267258492802366397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-693871129651954220708487756709446000000000000)
      constant := (18227847270820403018578998874016564505736113994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree103.table
  base := (41468371178230158875885475653441627067733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-70975189181035510882847305978500000000000)
      constant := (1869013344591391193658026924043691627067733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252486818413565574877/50000000000000000000)
  centralHi := (100994727365426229951/20000000000000000000)
  directionLo := (507442960290285783199/100000000000000000000)
  directionHi := (634303700362857229/125000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree104.table
  base := (43063072726903143961120523254845425304027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-700607987001401351528371079315308500000000000)
      constant := (18591216365723883457123959319801592513404768627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree104.table
  base := (43063072625264275018862278024064051088339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-71664293627980620799214350868500000000000)
      constant := (1906267916740679342721519140626064051088339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507442960290285783199/100000000000000000000)
  centralHi := (634303700362857229/125000000000000000)
  directionLo := (101980065111945827487/20000000000000000000)
  directionHi := (127475081389932284359/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree105.table
  base := (44683536894142581379829498255262137144373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-78593871594538720260917155769019000000000000)
      constant := (2106466431528261940423161687948723436100222197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree105.table
  base := (349090131304061086321317386439549466447/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-72353398074925730715581395758500000000000)
      constant := (1943892803848061474630484424723012331705216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101980065111945827487/20000000000000000000)
  centralHi := (127475081389932284359/25000000000000000000)
  directionLo := (512345904700786080907/100000000000000000000)
  directionHi := (128086476175196520227/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree106.table
  base := (9265952758140409057176599159214314544647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-142816340340059122633627544905406700000000000)
      constant := (3865758364967320727360965246857277746852085247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree106.table
  base := (46329763715856414327110711398127240426757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-73042502521870840631948440648500000000000)
      constant := (1981888005906197212745348969758627240426757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512345904700786080907/100000000000000000000)
  centralHi := (128086476175196520227/25000000000000000000)
  directionLo := (257389932845777877571/50000000000000000000)
  directionHi := (514779865691555755143/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree107.table
  base := (4800175341019491903304868593952591471331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-144163711809948548797604209426579200000000000)
      constant := (3940599637781605349272669876465071916771030262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree107.table
  base := (48001753345974953837268961770729138199377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-73731606968815950548315485538500000000000)
      constant := (2020253522908987450050573201677979138199377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257389932845777877571/50000000000000000000)
  centralHi := (514779865691555755143/100000000000000000000)
  directionLo := (129300593139389105261/25000000000000000000)
  directionHi := (103440474511511284209/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree108.table
  base := (24849752873662527647581541339703458993099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-8982165634557899688986473700478500000000000)
      constant := (247911320690329867315312300114919487076329958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree108.table
  base := (6212438211528299006114095883025527804701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-74420711415761060464682530428500000000000)
      constant := (2058989354851383141015466510963204222437608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129300593139389105261/25000000000000000000)
  centralHi := (103440474511511284209/20000000000000000000)
  directionLo := (5196135855007205261/1000000000000000000)
  directionHi := (519613585500720526101/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree109.table
  base := (51423020797718890166655342291605897255037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-734292273748637005627787692344621000000000000)
      constant := (20462248185819815855497167175895756117746617637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree109.table
  base := (25711510375224759050237307131430812339639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-75109815862706170381049575318500000000000)
      constant := (2098095501729223074778461384598611624679278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5196135855007205261/1000000000000000000)
  centralHi := (519613585500720526101/100000000000000000000)
  directionLo := (65251707627878383581/12500000000000000000)
  directionHi := (522013661023027068649/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree110.table
  base := (2658614927889147404527000230613531248789/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (2430)
      previous := (1215)
      next := (1215)
      square := (11163492040510780645146127218000000000000)
      linear := (-1224841539005097746194497545372700000000000)
      constant := (34458333584433218018677599152101284124607636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree110.table
  base := (53172298517233330239640798813746936692041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-75798920309651280297416620208500000000000)
      constant := (2137571963539096249587244118031246936692041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65251707627878383581/12500000000000000000)
  centralHi := (522013661023027068649/100000000000000000000)
  directionLo := (65550344005630156747/12500000000000000000)
  directionHi := (524402752045041253977/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree111.table
  base := (54947339024582910144904889925011583154543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-83085109827503474140839370839594000000000000)
      constant := (2359549763797200347799441774364967457805297327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree111.table
  base := (858552171715629590255312829861230598167/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-76488024756596390213783665098500000000000)
      constant := (2177418740278225130751743411655368758282688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65550344005630156747/12500000000000000000)
  centralHi := (524402752045041253977/100000000000000000000)
  directionLo := (65847626002451939709/12500000000000000000)
  directionHi := (526781008019615517673/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree112.table
  base := (11349628439148199077077742696483106773247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-150900569159395679617487532032441700000000000)
      constant := (4325643270514925982229313534175329929484593847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree112.table
  base := (56748142165907326786574778757704141306097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-77177129203541500130150709988500000000000)
      constant := (2217635831944366636347961763073704141306097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65847626002451939709/12500000000000000000)
  centralHi := (526781008019615517673/100000000000000000000)
  directionLo := (13228714376024778641/2500000000000000000)
  directionHi := (529148575040991145641/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree113.table
  base := (2928735403467444745880211060921004336083/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-152247940629285105781464196553614200000000000)
      constant := (4404819450752574781736166622939125397741797932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree113.table
  base := (58574708043761834688796630919438528537121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-77866233650486610046517754878500000000000)
      constant := (2258223238535728171794350731452188528537121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/2500000000000000000)
  centralHi := (529148575040991145641/100000000000000000000)
  directionLo := (106301119189905173241/20000000000000000000)
  directionHi := (265752797974762933103/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree114.table
  base := (30213518321946957183925053017374690860799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-85330728943985851080800478374881500000000000)
      constant := (2491510064191634356137902865541270826694820222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree114.table
  base := (1510675915548762988042531074159323186267/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-15711067619486343992576959953700000000000)
      constant := (459836192010179287825921196432174585490136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106301119189905173241/20000000000000000000)
  centralHi := (265752797974762933103/50000000000000000000)
  directionLo := (533852210432259853293/100000000000000000000)
  directionHi := (266926105216129926647/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree115.table
  base := (2492205116727853345294727337338901126739/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3920400000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (270156507380360891612536278675600000000000)
      linear := (-30988536713812791621883505119191840000000000)
      constant := (913067852977942934563620469205594413693168939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree115.table
  base := (31152563949689516617304116755586289016571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-79244442544376829879251844658500000000000)
      constant := (2340508996488777090303047133812422578033142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533852210432259853293/100000000000000000000)
  centralHi := (266926105216129926647/50000000000000000000)
  directionLo := (10723771102390409851/2000000000000000000)
  directionHi := (536188555119520492551/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree116.table
  base := (12841796378271258542597957709475467283983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-156290055038953384273394190117131700000000000)
      constant := (4646682898785129371477387970227469804850317383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree116.table
  base := (32104490937610417921556148655596102248249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-79933546991321939795618889548500000000000)
      constant := (2382207347848543585330268881164192204496498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10723771102390409851/2000000000000000000)
  centralHi := (536188555119520492551/100000000000000000000)
  directionLo := (269257381838877480879/50000000000000000000)
  directionHi := (538514763677754961759/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree117.table
  base := (66138598562708767146667121358064289319537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-9730705340052025335640176212241000000000000)
      constant := (291898087483326071362568872405969997757663977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree117.table
  base := (2066831204652308336721761273024528802163/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-80622651438267049711985934438500000000000)
      constant := (2424276014129593863639154150586534921669216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269257381838877480879/50000000000000000000)
  centralHi := (538514763677754961759/100000000000000000000)
  directionLo := (540830966898769105541/100000000000000000000)
  directionHi := (270415483449384552771/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree118.table
  base := (13618795586357082568510002997597611383491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-158984797978732236601347519159476700000000000)
      constant := (4811537620223055578519901137162340189169595291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree118.table
  base := (68093977919923847810490631304313976361527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-81311755885212159628352979328500000000000)
      constant := (2466714995331513647009633149595813976361527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540830966898769105541/100000000000000000000)
  centralHi := (270415483449384552771/50000000000000000000)
  directionLo := (543137292785541189259/100000000000000000000)
  directionHi := (27156864639277059463/5000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree119.table
  base := (35037559999141121925782695992316813179109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-801660847243108313826620918403246000000000000)
      constant := (24475243538820265827794355681809642765686894618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree119.table
  base := (70075119988113214363365492963910827647193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-82000860332157269544720024218500000000000)
      constant := (2509524291454045370855776262142160827647193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543137292785541189259/100000000000000000000)
  centralHi := (27156864639277059463/5000000000000000000)
  directionLo := (54543386663476984949/10000000000000000000)
  directionHi := (545433866634769849491/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree120.table
  base := (36041012381016131315143136040758298447483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-89821967176950604960722693445456500000000000)
      constant := (2766267933251415427003277868809509074018617974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree120.table
  base := (72082024753314823268729345308150311676901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-82689964779102379461087069108500000000000)
      constant := (2552703902497061892012591887818150311676901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54543386663476984949/10000000000000000000)
  centralHi := (545433866634769849491/100000000000000000000)
  directionLo := (136930202779076718501/25000000000000000000)
  directionHi := (109544162223261374801/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree121.table
  base := (74114692222982294898928169590385627146507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-6736649272247955169143698872851000000000000)
      constant := (209266046962332031216436143421561704548867067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree121.table
  base := (37057346107754856896004394188568820341649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-83379069226047489377454113998500000000000)
      constant := (2596253828460544249745506626663887640683298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136930202779076718501/25000000000000000000)
  centralHi := (109544162223261374801/20000000000000000000)
  directionLo := (274999123174808650601/50000000000000000000)
  directionHi := (549998246349617301203/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree122.table
  base := (76173122381173393776671330914640660759971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-821871419291449706286270886220833500000000000)
      constant := (25749584388358978991893258880979519366108475771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree122.table
  base := (3046924894990732309292985693844993118707/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-3362726946919703971752846355540000000000)
      constant := (105606962773782514634145651954184993118707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274999123174808650601/50000000000000000000)
  centralHi := (549998246349617301203/100000000000000000000)
  directionLo := (138066572494350422477/25000000000000000000)
  directionHi := (552266289977401689909/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree123.table
  base := (9782164404590534189314629949070956800433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-92067586293432981900683800980744000000000000)
      constant := (2909065501890479111724113442239553519395372296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree123.table
  base := (78257315231234527173441464758352210346389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-84757278119937709210188203778500000000000)
      constant := (2684464625149261662420760461933602210346389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138066572494350422477/25000000000000000000)
  centralHi := (552266289977401689909/100000000000000000000)
  directionLo := (554525057236508239933/100000000000000000000)
  directionHi := (277262528618254119967/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree124.table
  base := (20091817697454328597594687406750078412607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-835345133990343967926037531432558500000000000)
      constant := (26617207068409962327163889414220126324087844828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree124.table
  base := (80367270785112387136732671562317301214397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-85446382566882819126555248668500000000000)
      constant := (2729125495874844654468237531849317301214397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554525057236508239933/100000000000000000000)
  centralHi := (277262528618254119967/50000000000000000000)
  directionLo := (27838733051312785487/5000000000000000000)
  directionHi := (556774661026255709741/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree125.table
  base := (16500597808137349870256404689856101384533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-168416398267958219749184170807684200000000000)
      constant := (5411287408509645134789532344112306993419807933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree125.table
  base := (41251494518327343610075048817756978763833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-86135487013827929042922293558500000000000)
      constant := (2774156681521564641594024343479263957527666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27838733051312785487/5000000000000000000)
  centralHi := (556774661026255709741/100000000000000000000)
  directionLo := (139753802993570437499/25000000000000000000)
  directionHi := (559015211974281749997/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree126.table
  base := (84664469989608701624358480468818595794943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-10479245045546150982293878724003500000000000)
      constant := (339497277030022325057005616061874550091188103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree126.table
  base := (84664469986153483058063978494858093253909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-86824591460773038959289338448500000000000)
      constant := (2819558182089713679432491132340358093253909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139753802993570437499/25000000000000000000)
  centralHi := (559015211974281749997/100000000000000000000)
  directionLo := (4384740769531447837/781250000000000000)
  directionHi := (561246818500025323137/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree127.table
  base := (86851713636892792335003852189060608076147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-855555706038685360385687499250146000000000000)
      constant := (27945734259063744890823272520036311613504316747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree127.table
  base := (10856464204241508328751278411604641330273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-87513695907718148875656383338500000000000)
      constant := (2865329997579615059963173811585087130642184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4384740769531447837/781250000000000000)
  centralHi := (561246818500025323137/100000000000000000000)
  directionLo := (563469586875946283821/100000000000000000000)
  directionHi := (281734793437973141911/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree128.table
  base := (890647199828750794946423416403316142621/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3920400000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (270156507380360891612536278675600000000000)
      linear := (-34491702535525299648222832874240340000000000)
      constant := (1135832060057893162485403327661406806055313684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree128.table
  base := (89064719980338225373000810824091646489649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-88202800354663258792023428228500000000000)
      constant := (2911472127991616570623084348008091646489649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563469586875946283821/100000000000000000000)
  centralHi := (281734793437973141911/50000000000000000000)
  directionLo := (565683621286579929769/100000000000000000000)
  directionHi := (56568362128657992977/10000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree129.table
  base := (91303489027912125679417518026777104460541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-96558824526397735780606016051319000000000000)
      constant := (3205497907398450612595741115253138235507529149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree129.table
  base := (22825872256434646202048706720117976946861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-88891904801608368708390473118500000000000)
      constant := (2957984573326084836933381839401221907787444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565683621286579929769/100000000000000000000)
  centralHi := (56568362128657992977/10000000000000000000)
  directionLo := (567889023885519374899/100000000000000000000)
  directionHi := (5678890238855193749/1000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree130.table
  base := (4678401038618801113618162887931487146153/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-175153255617405350569067493413546700000000000)
      constant := (5861354650896714222429629615992444772077782212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree130.table
  base := (23392005192628467227231163714532669283013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-89581009248553478624757518008500000000000)
      constant := (3004867333583400582867398665160630677132052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567889023885519374899/100000000000000000000)
  centralHi := (5678890238855193749/1000000000000000000)
  directionLo := (570085894850413926961/100000000000000000000)
  directionHi := (285042947425206963481/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree131.table
  base := (3834332608666008963940917705687839992923/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3920400000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (270156507380360891612536278675600000000000)
      linear := (-35300125417458955346608831586943840000000000)
      constant := (1190707110605745363969390700186828763520638323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree131.table
  base := (95858315215054937503364379139734539309157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-90270113695498588541124562898500000000000)
      constant := (3052120408763954668253308909668984539309157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570085894850413926961/100000000000000000000)
  centralHi := (285042947425206963481/50000000000000000000)
  directionLo := (143068583109016812727/25000000000000000000)
  directionHi := (572274332436067250909/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree132.table
  base := (1963487447222521406718965758820618388779/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3600000000000000000000000000000000000000
      center := (54)
      previous := (27)
      next := (27)
      square := (248077600900239569892136160400000000000)
      linear := (-32662625997646318254732933417060000000000)
      constant := (1110457105548946923412511043992721130998022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree132.table
  base := (98174372359759481292317445072500625242903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-90959218142443698457491607788500000000000)
      constant := (3099743798868144783791916018273500625242903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143068583109016812727/25000000000000000000)
  centralHi := (572274332436067250909/100000000000000000000)
  directionLo := (57445443302571494987/10000000000000000000)
  directionHi := (574454433025714949871/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree133.table
  base := (12564524025774985790299876574105919980983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-895976850135368145304987434885321000000000000)
      constant := (30700324054766793168796068089364088692618915064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree133.table
  base := (50258096102514636570137602730588462127117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-91648322589388808373858652678500000000000)
      constant := (3147737503896372702347711343778926924254234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57445443302571494987/10000000000000000000)
  centralHi := (574454433025714949871/100000000000000000000)
  directionLo := (576626291180557281533/100000000000000000000)
  directionHi := (288313145590278640767/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree134.table
  base := (20576754950454115359289793923537943392453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-180542741496963055224974151498236700000000000)
      constant := (6234413166747536660249778917621388383189431853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree134.table
  base := (102883774751267889649729007179002303578053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-92337427036333918290225697568500000000000)
      constant := (3196101523849042000523186233058502303578053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576626291180557281533/100000000000000000000)
  centralHi := (288313145590278640767/50000000000000000000)
  directionLo := (115757999937523806791/20000000000000000000)
  directionHi := (144697499921904758489/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree135.table
  base := (10527711999973763463614937775262405057727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 242000000000000000000000000000000000000000
      center := (3630)
      previous := (1815)
      next := (1815)
      square := (16676327616071659976082486338000000000000)
      linear := (-2245556950208055325789516247153200000000000)
      constant := (78141777865399174856695981885857720773969934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree135.table
  base := (105277119998878830065439069906328887103301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-93026531483279028206592742458500000000000)
      constant := (3244835858726556177563100905792578887103301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115757999937523806791/20000000000000000000)
  centralHi := (144697499921904758489/25000000000000000000)
  directionLo := (580945649606005097493/100000000000000000000)
  directionHi := (290472824803002548747/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree136.table
  base := (6731014246812468790516779921736208616191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-916187422183709537764637402702908500000000000)
      constant := (32126386660017645834282137853753407790356607856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree136.table
  base := (4307849117930558825031324108760232963137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-3748625437208965524918391493940000000000)
      constant := (131757620341172684388233322842280232963137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580945649606005097493/100000000000000000000)
  centralHi := (290472824803002548747/50000000000000000000)
  directionLo := (291546665155808487749/50000000000000000000)
  directionHi := (583093330311616975499/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree137.table
  base := (110141098600452219722172609312090415040347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-922924279533156668584520725308771000000000000)
      constant := (32608965707334504989170369624134304876560440947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree137.table
  base := (27535274649955575469664940815501151932291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-94404740377169248039326832238500000000000)
      constant := (3343415473257723787499281386496754607729164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291546665155808487749/50000000000000000000)
  centralHi := (583093330311616975499/100000000000000000000)
  directionLo := (292616564770196181907/50000000000000000000)
  directionHi := (117046625908078472763/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree138.table
  base := (109972394486805026322681056055153843693/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-103295681875844866600489338657181500000000000)
      constant := (3677239686382343412680887570189471286640437248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree138.table
  base := (56305865976974452230648807029169404720197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-95093844824114357955693877128500000000000)
      constant := (3393260752912171291580674414634838809440394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292616564770196181907/50000000000000000000)
  centralHi := (117046625908078472763/20000000000000000000)
  directionLo := (587365133430126986527/100000000000000000000)
  directionHi := (18355160419691468329/3125000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree139.table
  base := (14388516001437008049237761012507804019879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-936397994232050930224287370520496000000000000)
      constant := (33584961070341207581416019535953097991340672632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree139.table
  base := (115108128011034125620402587550212591673751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-95782949271059467872060922018500000000000)
      constant := (3443476347493049969196718087913462591673751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587365133430126986527/100000000000000000000)
  centralHi := (18355160419691468329/3125000000000000000)
  directionLo := (147372356640233773131/25000000000000000000)
  directionHi := (23579577062437403701/4000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree140.table
  base := (117630286771858475040214688042198091946959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-943134851581498061044170693126358500000000000)
      constant := (34078377386038610383533661231483764749172145159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree140.table
  base := (58815143385731462251429295889380925263103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-96472053718004577788427966908500000000000)
      constant := (3494062257000744779494296314373761850526206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147372356640233773131/25000000000000000000)
  centralHi := (23579577062437403701/4000000000000000000)
  directionLo := (591606091994402384391/100000000000000000000)
  directionHi := (73950761499300298049/12500000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree141.table
  base := (24035641647190609161981696119714489748349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-21108260198465448708090089238493800000000000)
      constant := (768342358323044414971777188920425673085952061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree141.table
  base := (120178208235614359131832199533420495513499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-97161158164949687704795011798500000000000)
      constant := (3545018481435634780496575666805170495513499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591606091994402384391/100000000000000000000)
  centralHi := (73950761499300298049/12500000000000000000)
  directionLo := (296857605655741329481/50000000000000000000)
  directionHi := (593715211311482658963/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree142.table
  base := (15343986550518896937582834808170307368569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-956608566280392322683937338338083500000000000)
      constant := (35076047285840012531621010309394499960154758152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree142.table
  base := (122751892403861192129561994796434325117939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-97850262611894797621162056688500000000000)
      constant := (3596345020798092734825794729189934325117939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296857605655741329481/50000000000000000000)
  centralHi := (593715211311482658963/100000000000000000000)
  directionLo := (595816864649187078999/100000000000000000000)
  directionHi := (595816864649187079/100000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree143.table
  base := (62675669638408933724352665381826224801871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-7961532426692888045486121164826000000000000)
      constant := (294052073305382060784340022849963192167903102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree143.table
  base := (125351339276569595767557002364880944552193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-98539367058839907537529101578500000000000)
      constant := (3648041875088484814753462526325130944552193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595816864649187078999/100000000000000000000)
  centralHi := (595816864649187079/100000000000000000)
  directionLo := (298955565368056379993/50000000000000000000)
  directionHi := (597911130736112759987/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree144.table
  base := (127976548854311489686643557188455055447273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-11976324456534402275601283747528500000000000)
      constant := (445532924405853845786048805529668061709120033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree144.table
  base := (127976548854098939911860578560506509682869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-99228471505785017453896146468500000000000)
      constant := (3700109044307170390145622414532506509682869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298955565368056379993/50000000000000000000)
  centralHi := (597911130736112759987/100000000000000000000)
  directionLo := (23999923477074209507/4000000000000000000)
  directionHi := (149999521731713809419/25000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree145.table
  base := (26125504227396721610206935674773437900683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-195363827665746743028717461231134200000000000)
      constant := (7319929061322450937935908011620396808614594083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree145.table
  base := (32656880284200412241426407416099168590783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-99917575952730127370263191358500000000000)
      constant := (3752546528454501885405507300093146674363132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23999923477074209507/4000000000000000000)
  centralHi := (149999521731713809419/25000000000000000000)
  directionLo := (120415561847069474749/20000000000000000000)
  directionHi := (301038904617673686873/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree146.table
  base := (13330425612517887993191871214078496731327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-196711199135636169192694125752306700000000000)
      constant := (7422947231833777377002737082020952442927471854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree146.table
  base := (65089968811046443389873934449372623289/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-100606680399675237286630236248500000000000)
      constant := (3805354327530824693666486845082815132495872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120415561847069474749/20000000000000000000)
  centralHi := (301038904617673686873/50000000000000000000)
  directionLo := (151037593091791338097/25000000000000000000)
  directionHi := (604150372367165352389/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree147.table
  base := (17000844227404374782528394906132315968791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-110032539225291997420372661263044000000000000)
      constant := (4181493270505263091454272104762082080470107192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree147.table
  base := (68003376909550832293080184372418388823377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-101295784846620347202997281138500000000000)
      constant := (3858532441536477138312592275422086777646754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151037593091791338097/25000000000000000000)
  centralHi := (604150372367165352389/100000000000000000000)
  directionLo := (606215849750840613783/100000000000000000000)
  directionHi := (75776981218855076723/12500000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree148.table
  base := (138735014219482676944491938276483151925359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-997029710377075107603237273973258500000000000)
      constant := (38155755132750938830921351990344885122020443559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree148.table
  base := (138735014219368548644264910285652208397883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-101984889293565457119364326028500000000000)
      constant := (3912080870471790473451287218754652208397883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606215849750840613783/100000000000000000000)
  centralHi := (75776981218855076723/12500000000000000000)
  directionLo := (304137156784107427779/50000000000000000000)
  directionHi := (608274313568214855559/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree149.table
  base := (141489037326245670338955864763650837467683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1003766567726522238423120596579121000000000000)
      constant := (38681683253782773024938328387676543576770761083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree149.table
  base := (141489037326147985429519974699656964283701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-102673993740510567035731370918500000000000)
      constant := (3965999614337088916275316207405406964283701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304137156784107427779/50000000000000000000)
  centralHi := (608274313568214855559/100000000000000000000)
  directionLo := (610325834783873605271/100000000000000000000)
  directionHi := (76290729347984200659/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree150.table
  base := (72134411569920410243937922491136789375173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-112278158341774374360333768798331500000000000)
      constant := (4356802644182886197112793341469195927259126794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree150.table
  base := (28853764627951442704028899366553186466311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-20672619637491135390419683161700000000000)
      constant := (804057734626537941072579635244053186466311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610325834783873605271/100000000000000000000)
  centralHi := (76290729347984200659/12500000000000000000)
  directionLo := (306185241586846160343/50000000000000000000)
  directionHi := (612370483173692320687/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree151.table
  base := (73537185830289063438411373577597285306707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1017240282425416500062887241790846000000000000)
      constant := (39744376764343585383109867126435630580332070614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree151.table
  base := (73537185830253286055247198743147881939523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-104052202634400786868465460698500000000000)
      constant := (4074948046858903179908389046000545763879046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306185241586846160343/50000000000000000000)
  centralHi := (612370483173692320687/100000000000000000000)
  directionLo := (307204163676263752767/50000000000000000000)
  directionHi := (122881665470505501107/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree152.table
  base := (149905682888760834257726057994639326068073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1023977139774863630882770564396708500000000000)
      constant := (40281142153878573954036170446581667534793183473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree152.table
  base := (149905682888699596963205235386059623300599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-104741307081345896784832505588500000000000)
      constant := (4129977735516032875674424375472059623300599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307204163676263752767/50000000000000000000)
  centralHi := (122881665470505501107/20000000000000000000)
  directionLo := (61643943480108393223/10000000000000000000)
  directionHi := (616439434801083932231/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree153.table
  base := (76381378412342767411449406352646366696893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-12724864162028527922254986259291000000000000)
      constant := (503969382299430226998406297428419639490648106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree153.table
  base := (6110510272985325182019828926104597848059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-4217216461131640268047982019140000000000)
      constant := (167415109564175025365328915090214597848059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61643943480108393223/10000000000000000000)
  centralHi := (616439434801083932231/100000000000000000000)
  directionLo := (618463871891987735571/100000000000000000000)
  directionHi := (154615967972996933893/25000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree154.table
  base := (155645593468642281603524235621500600519839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (12150)
      previous := (6075)
      next := (6075)
      square := (55817460202553903225730636090000000000000)
      linear := (-8573974003915354483657332310813500000000000)
      constant := (341863720673324392490683577218987798642106959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree154.table
  base := (155645593468597436425242464421978839206083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-106119515975236116617566595368500000000000)
      constant := (4241148057624221721837661154986478839206083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618463871891987735571/100000000000000000000)
  centralHi := (154615967972996933893/25000000000000000000)
  directionLo := (77560212989386734873/12500000000000000000)
  directionHi := (124096340783018775797/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree155.table
  base := (9909637051307169404776159579649642548929/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1044187711823205023342420532214296000000000000)
      constant := (41913112859536563182770254538199884439702850064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree155.table
  base := (158554192820876336347319309341585072722337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-106808620422181226533933640258500000000000)
      constant := (4297288691075854957547613058812835072722337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77560212989386734873/12500000000000000000)
  centralHi := (124096340783018775797/20000000000000000000)
  directionLo := (622492995102055293783/100000000000000000000)
  directionHi := (77811624387756911723/12500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree156.table
  base := (161488554881780168593179598624421633271613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-116769396574739128240255983868906500000000000)
      constant := (4718258660049944637832927281850491408632786557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree156.table
  base := (161488554881747333100860736248743180708343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-107497724869126336450300685148500000000000)
      constant := (4353799639459552845047213067071743180708343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622492995102055293783/100000000000000000000)
  centralHi := (77811624387756911723/12500000000000000000)
  directionLo := (624497808650179848843/100000000000000000000)
  directionHi := (156124452162544962211/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree157.table
  base := (32889735930301969481975568847651475193071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-211532285304419856996437435485204200000000000)
      constant := (8603831088842745022402386508097423452117288871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree157.table
  base := (32889735930296350456975707040984784390363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (137820889389021983273408978000000000000)
      linear := (-21637365863214289273333546007700000000000)
      constant := (882136180555117341987094593964934784390363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624497808650179848843/100000000000000000000)
  centralHi := (156124452162544962211/25000000000000000000)
  directionLo := (313248103372800109961/50000000000000000000)
  directionHi := (626496206745600219923/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree158.table
  base := (167434567130368918803262943014779381619997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1064398283871546415802070500031883500000000000)
      constant := (43577595370831832246881038897759870219257590597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree158.table
  base := (3348691342606897613052989658981019723311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-4355037350520662251321390997140000000000)
      constant := (178717299240968873558626781752422039446622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313248103372800109961/50000000000000000000)
  centralHi := (626496206745600219923/100000000000000000000)
  directionLo := (125697650117156138309/20000000000000000000)
  directionHi := (314244125292890345773/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree159.table
  base := (8522310865930833650977796335042926139301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178000000000000000000000000000000000000000
      center := (32670)
      previous := (16335)
      next := (16335)
      square := (150086948544644939784742377042000000000000)
      linear := (-23803003138244301036043418280838800000000000)
      constant := (980881060451252543306819487569416955012795156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree159.table
  base := (42611554329649026705665929875097804760923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-109565038209961666199401819818500000000000)
      constant := (4525554374205717620756292929048641219043692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125697650117156138309/20000000000000000000)
  centralHi := (314244125292890345773/50000000000000000000)
  directionLo := (315237000200691968611/50000000000000000000)
  directionHi := (630474000401383937223/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree160.table
  base := (8674181510825332871075296538032588689783/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-215574399714088135488367429048721700000000000)
      constant := (8941062498527961347098350189152599606994252732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree160.table
  base := (86741815108244531196306398301503046255949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-110254142656906776115768864708500000000000)
      constant := (4583546582320327686905034677283006092511898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315237000200691968611/50000000000000000000)
  centralHi := (630474000401383937223/100000000000000000000)
  directionLo := (632453515477519883077/100000000000000000000)
  directionHi := (316226757738759941539/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree161.table
  base := (176546805824286815184653794015815405920159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1084608855919887808261720467849471000000000000)
      constant := (45274589687834589197999136674468628512173478359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree161.table
  base := (88273402912135881331895259082318945704867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-110943247103851886032135909598500000000000)
      constant := (4641909105368300052713188592421387891409734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632453515477519883077/100000000000000000000)
  centralHi := (316226757738759941539/50000000000000000000)
  directionLo := (39651678385899866457/6250000000000000000)
  directionHi := (634426854174397863313/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree162.table
  base := (89817872071099811624940698857796670707879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (18150)
      previous := (9075)
      next := (9075)
      square := (83381638080358299880412431690000000000000)
      linear := (-13473403867522653568908688771053500000000000)
      constant := (566018263035717140158353301788450544311306718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree162.table
  base := (179635744142186746331377574362139574300081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-111632351550796995948502954488500000000000)
      constant := (4700641943349877256875935364640639574300081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39651678385899866457/6250000000000000000)
  centralHi := (634426854174397863313/100000000000000000000)
  directionLo := (63639407394740242099/10000000000000000000)
  directionHi := (636394073947402420991/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree163.table
  base := (36550089034096445794153541912627395176441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19602000000000000000000000000000000000000000
      center := (294030)
      previous := (147015)
      next := (147015)
      square := (1350782536901804458062681393378000000000000)
      linear := (-219616514123756413980297422612239200000000000)
      constant := (9284796269363525696237324143881836318874298241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree163.table
  base := (7310017806818848544825066622418658922273/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-4492858239909684234594799975140000000000)
      constant := (190389803850611859984741107772228658922273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63639407394740242099/10000000000000000000)
  centralHi := (636394073947402420991/100000000000000000000)
  directionLo := (127671046273322458441/20000000000000000000)
  directionHi := (319177615683306146103/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree164.table
  base := (185890908909366585004784824191125593004501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1104819427968229200721370435667058500000000000)
      constant := (47004095810610482951075030497597580687037114301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree164.table
  base := (185890908909357162453561104498700619186651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-113010560444687215781237044268500000000000)
      constant := (4819218564114789778862988894155700619186651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127671046273322458441/20000000000000000000)
  centralHi := (319177615683306146103/50000000000000000000)
  directionLo := (20009699441743166679/3125000000000000000)
  directionHi := (640310382135781333729/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree165.table
  base := (47264283839769895522536732089113612716283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1350)
      previous := (675)
      next := (675)
      square := (6201940022505989247303404010000000000000)
      linear := (-1020712842348646769092060384089000000000000)
      constant := (43698643431840106077701638222069808807786188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree165.table
  base := (3781142707181430446370097434889011781839/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-4547986595665293027904163566340000000000)
      constant := (195162493875943360963905717790328023563678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20009699441743166679/3125000000000000000)
  centralHi := (640310382135781333729/100000000000000000000)
  directionLo := (642259581110799411809/100000000000000000000)
  directionHi := (64225958111079941181/10000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree166.table
  base := (96124562259921589713943412908894962872409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1118293142667123462361137080878783500000000000)
      constant := (48175162006809981605942103807757194062224961218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree166.table
  base := (24031140564979535698521399557967550455133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-114388769338577435613971134048500000000000)
      constant := (4939276444616901227695203075279240403641064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642259581110799411809/100000000000000000000)
  centralHi := (64225958111079941181/10000000000000000000)
  directionLo := (8052536028970632013/1250000000000000000)
  directionHi := (644202882317650561041/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree167.table
  base := (48866719097968633113445854025985640664337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1125030000016570593181020403484646000000000000)
      constant := (48766113739220929553476158843648969650354667748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree167.table
  base := (195466876391868636093352460247128030293713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-115077873785522545530338178938500000000000)
      constant := (4999860857269958573486461667309378030293713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8052536028970632013/1250000000000000000)
  centralHi := (644202882317650561041/100000000000000000000)
  directionLo := (323070169484942522737/50000000000000000000)
  directionHi := (25845613558795401819/4000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree168.table
  base := (198710390975386117839055924028115235635517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (163350)
      previous := (81675)
      next := (81675)
      square := (750434742723224698923711885210000000000000)
      linear := (-125751873040668636000100414010056500000000000)
      constant := (5484519766056533538341540972655949991607078013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree168.table
  base := (3974207819507621496206904027168041968409/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (27564177877804396654681795600000000000)
      linear := (-4630679129298706217868208953140000000000)
      constant := (202432623394318742497908610364496083936818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell066.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323070169484942522737/50000000000000000000)
  centralHi := (25845613558795401819/4000000000000000000)
  directionLo := (648072003485621307711/100000000000000000000)
  directionHi := (10126125054462832933/1562500000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree169.table
  base := (201979668270585855603937589059770084170413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1470150)
      previous := (735075)
      next := (735075)
      square := (6753912684509022290313406966890000000000000)
      linear := (-1138503714715464854820787048696371000000000000)
      constant := (49958854472675636304853539518561133313704217813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree169.table
  base := (100989834135290771281347792352484282504377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (689104446945109916367044890000000000000)
      linear := (-116456082679412765363072268718500000000000)
      constant := (5122140627381139135402510015595718565008754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell066.Kernel169
