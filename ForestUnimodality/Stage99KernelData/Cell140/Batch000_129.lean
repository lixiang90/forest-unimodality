import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell140.Parameters
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch000_049
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch050_099
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree000.table
  base := (2759765429272717504105116837/50000000000000000000000000)
  polynomial :=
    { denominator := 1806240000000000000000000000000000000000000000
      center := (11376281)
      previous := (0)
      next := (10117975)
      square := (264590600381923192601085765139200000000000000)
      linear := (-1219203282627070572026184427492800000000000000)
      constant := (99695974179391065292296524713257600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree000.table
  base := (2759765429272717504105116837/50000000000000000000000000)
  polynomial :=
    { denominator := 225780000000000000000000000000000000000000000
      center := (1422407)
      previous := (0)
      next := (1264375)
      square := (33073825047740399075135720642400000000000000)
      linear := (-152400410328383821503273053436600000000000000)
      constant := (12461996772423883161537065589157200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree001.table
  base := (331242336065551631928359586090396929760851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-16925410458315934098787495759659016800000000000000)
      constant := (683545828097440376705812302778704603934248283109936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree001.table
  base := (16559242903597881957303950986238499601693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-2115779662992765951095546769084384600000000000000)
      constant := (85428871182269193682005585208057146819906003802120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49913435199935546641/100000000000000000000)
  directionHi := (24956717599967773321/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree002.table
  base := (51951439559786849798785167596906804443859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-20087235059054868509971395517351814400000000000000)
      constant := (441645559825290399290456500047274641528796804450496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree002.table
  base := (103870834116320501616585990583424541530683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-2511111093788406941240644037922991800000000000000)
      constant := (55190054614836633664832816214164598045591638755372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/100000000000000000000)
  centralHi := (24956717599967773321/50000000000000000000)
  directionLo := (70588257004379487127/100000000000000000000)
  directionHi := (8823532125547435891/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree003.table
  base := (68592964456166398006945438356528533671369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-7749686553264600973718431758348204000000000000000)
      constant := (103038500346948984308757306525800657575442448130656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree003.table
  base := (68565602838165757491232173273293320063491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-968814174861349310461913768920533000000000000000)
      constant := (12875565458299636658581787158407024884041479479748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70588257004379487127/100000000000000000000)
  centralHi := (8823532125547435891/12500000000000000000)
  directionLo := (17290521149317037967/20000000000000000000)
  directionHi := (21613151436646297459/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree004.table
  base := (95454129386993088606113126171471517155049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-26410884260532737332339195032737409600000000000000)
      constant := (237163454840607933529390644113675488870672598232464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree004.table
  base := (47705673370497557565192851460349192285877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-3301773955379688921530838575600206200000000000000)
      constant := (29636355151536601682036114359046106224134526795668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/20000000000000000000)
  centralHi := (21613151436646297459/25000000000000000000)
  directionLo := (49913435199935546641/50000000000000000000)
  directionHi := (99826870399871093283/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree005.table
  base := (17424523285011915467952036096194778140579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-29572708861271671743523094790430207200000000000000)
      constant := (199460479060432937996461079645850325038548133162176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree005.table
  base := (69665457915298653505624750617614411504407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-3697105386175329911675935844438813400000000000000)
      constant := (24926800102981973992598429676376354487283052566094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/50000000000000000000)
  centralHi := (99826870399871093283/100000000000000000000)
  directionLo := (55804917048793344467/50000000000000000000)
  directionHi := (22321966819517337787/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree006.table
  base := (52924456871293718011636867645219004975719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-10911511154003535384902331516041001600000000000000)
      constant := (60582218668729059922477218998599802818465052952528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree006.table
  base := (3306208381712590451182098536654578885379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-1364145605656990300607011037759140200000000000000)
      constant := (7571775653018261424419450865272250037516633828896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/50000000000000000000)
  centralHi := (22321966819517337787/20000000000000000000)
  directionLo := (122262447549314949813/100000000000000000000)
  directionHi := (61131223774657474907/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree007.table
  base := (41324849513586407579311530446618740540901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-35896358062749540565890894305815802400000000000000)
      constant := (176256472056601334990287645926755500601188578406736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree007.table
  base := (41304948808176194630050830008952134719877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-4487768247766611891966130382116027800000000000000)
      constant := (22031334339092025116709773328283988029796067625834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122262447549314949813/100000000000000000000)
  centralHi := (61131223774657474907/50000000000000000000)
  directionLo := (26411707323993391579/20000000000000000000)
  directionHi := (16507317077495869737/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree008.table
  base := (16404174966639346633179330693341844232043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-39058182663488474977074794063508600000000000000000)
      constant := (178726404498667040277259360300183711260052379436896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree008.table
  base := (16395993236114028004926422577131013177773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-4883099678562252882111227650954635000000000000000)
      constant := (22342036258143570681675902975603414142585738050932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26411707323993391579/20000000000000000000)
  centralHi := (16507317077495869737/12500000000000000000)
  directionLo := (28235302801751794851/20000000000000000000)
  directionHi := (8823532125547435891/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree009.table
  base := (1638304783871158091266696821497934548847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-14073335754742469796086231273733799200000000000000)
      constant := (62262298069963427086783372538931947651486227309824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree009.table
  base := (5239782264415901654796144965252978186711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-1759477036452631290752108306597747400000000000000)
      constant := (7783792314618038265931740287166030866314239424770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28235302801751794851/20000000000000000000)
  centralHi := (8823532125547435891/6250000000000000000)
  directionLo := (37435076399951659981/25000000000000000000)
  directionHi := (5989612223992265597/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree010.table
  base := (1044042391184423777248717361252013964531/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-45381831864966343799442593578894195200000000000000)
      constant := (199097090173232551032388706670066884164982621328320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree010.table
  base := (20868549450712596583148015751036418729559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-5673762540153534862401422188631849400000000000000)
      constant := (24891853911679895987011774666119336058575773238478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/25000000000000000000)
  centralHi := (5989612223992265597/4000000000000000000)
  directionLo := (7892007053750910173/5000000000000000000)
  directionHi := (157840141075018203461/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree011.table
  base := (2053806325684060524936227571297160983313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-48543656465705278210626493336586992800000000000000)
      constant := (214878450764500267372015187132992556127993835401344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree011.table
  base := (16419365005821214973299535087372985922867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-6069093970949175852546519457470456600000000000000)
      constant := (26866220142953071246032836731034961940643518321414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7892007053750910173/5000000000000000000)
  centralHi := (157840141075018203461/100000000000000000000)
  directionLo := (165544136555904067731/100000000000000000000)
  directionHi := (41386034138976016933/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree012.table
  base := (12632048538987143744125419720779560592347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-17235160355481404207270131031426596800000000000000)
      constant := (77887577565206223138683865947161225907201934078864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree012.table
  base := (3155474893316048227325366600798614045041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-2154808467248272280897205575436354600000000000000)
      constant := (9738663526354947737140910682322266236245300126296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165544136555904067731/100000000000000000000)
  centralHi := (41386034138976016933/25000000000000000000)
  directionLo := (17290521149317037967/10000000000000000000)
  directionHi := (172905211493170379671/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree013.table
  base := (4670585345583127183007755538827624154747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-54867305667183147032994292851972588000000000000000)
      constant := (255155350439383825999033751364608269506113505605984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree013.table
  base := (93317915327290656196957840858481991729/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-6859756832540457832836713995147671000000000000000)
      constant := (31904369891081921871714404270448030255410635961800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/10000000000000000000)
  centralHi := (172905211493170379671/100000000000000000000)
  directionLo := (89982724973958394813/50000000000000000000)
  directionHi := (179965449947916789627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree014.table
  base := (3230997038333691697121538809599026994303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-58029130267922081444178192609665385600000000000000)
      constant := (279160914763814931914213533877696176908769044955616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree014.table
  base := (1290656523317335565862074905482193566291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-7255088263336098822981811263986278200000000000000)
      constant := (34906950920454338002481638011521584065045393686110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/50000000000000000000)
  centralHi := (179965449947916789627/100000000000000000000)
  directionLo := (46689743378775324503/25000000000000000000)
  directionHi := (186758973515101298013/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree015.table
  base := (392729423810235072387919425152335855443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-20396984956220338618454030789119394400000000000000)
      constant := (101847450225114932467228545468997273824759575936160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree015.table
  base := (30618635464524329894010010411036039311/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-2550139898043913271042302844274961800000000000000)
      constant := (12735536238841546009818970532129883372372021933312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46689743378775324503/25000000000000000000)
  centralHi := (186758973515101298013/100000000000000000000)
  directionLo := (193313903281353441673/100000000000000000000)
  directionHi := (96656951640676720837/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree016.table
  base := (421828618972883516797960510267034509063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-64352779469399950266545992125050980800000000000000)
      constant := (334198201062383548462184968819790087615646528308672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree016.table
  base := (1679763327004452355401286649848335521661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-8045751124927380803272005801663492600000000000000)
      constant := (41790666320902502009012673931526492596397612572762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/100000000000000000000)
  centralHi := (96656951640676720837/50000000000000000000)
  directionLo := (39930748159948437313/20000000000000000000)
  directionHi := (99826870399871093283/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree017.table
  base := (-59303018118334751056470312480650756429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-67514604070138884677729891882743778400000000000000)
      constant := (365049819456901693063386216530624100737471016919280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree017.table
  base := (-303542619016252483973281959088898002991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-8441082555723021793417103070502099800000000000000)
      constant := (45649295647843706673095313094982345828569928821378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39930748159948437313/20000000000000000000)
  centralHi := (99826870399871093283/50000000000000000000)
  directionLo := (205798365466756811823/100000000000000000000)
  directionHi := (12862397841672300739/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree018.table
  base := (-2055205352834583311075842372468651566067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-23558809556959273029637930546812192000000000000000)
      constant := (132677990885346630076826009789177144537874077504496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree018.table
  base := (-2061738076954290375869115402038196136073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-2945471328839554261187400113113569000000000000000)
      constant := (16591531300406368620141642758863145389548355941978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205798365466756811823/100000000000000000000)
  centralHi := (12862397841672300739/6250000000000000000)
  directionLo := (211764771013138461383/100000000000000000000)
  directionHi := (26470596376642307673/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree019.table
  base := (-144574869356534316236817730731280094311/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-73838253271616753500097691398129373600000000000000)
      constant := (433098429164151983955030803308003794976593085187600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree019.table
  base := (-28963487965997705514047323578946522881/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-9231745417314303773707297608179314200000000000000)
      constant := (54160032774688268475000736483793155586596014499750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211764771013138461383/100000000000000000000)
  centralHi := (26470596376642307673/12500000000000000000)
  directionLo := (217567619961484922237/100000000000000000000)
  directionHi := (108783809980742461119/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree020.table
  base := (-4995578901908857855493201378752247273299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-77000077872355687911281591155822171200000000000000)
      constant := (470199217235636614403149769857691768405162764035536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree020.table
  base := (-5001199956092748962716800177738660768389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-9627076848109944763852394877017921400000000000000)
      constant := (58800116077208456734674979209840067462346954240662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/100000000000000000000)
  centralHi := (108783809980742461119/50000000000000000000)
  directionLo := (55804917048793344467/25000000000000000000)
  directionHi := (223219668195173377869/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree021.table
  base := (-3108609442085743683778320183040916698009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-26720634157698207440821830304504989600000000000000)
      constant := (169766278114485611926534010886547410946561977261984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree021.table
  base := (-1555605370370524306147596561214399367513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-3340802759635195251332497381952176200000000000000)
      constant := (21230052040441102540206914878823629733340547447272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/25000000000000000000)
  centralHi := (223219668195173377869/100000000000000000000)
  directionLo := (45746418999795584927/20000000000000000000)
  directionHi := (57183023749744481159/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree022.table
  base := (-911889517574186377350587074573131856757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-83323727073833556733649390671207766400000000000000)
      constant := (550365013395809909765061569281850279356490725453184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree022.table
  base := (-364996234471929319764620893764024884677/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-10417739709701226744142589414695135800000000000000)
      constant := (68826119607822146886682412970527250344596541051320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45746418999795584927/20000000000000000000)
  centralHi := (57183023749744481159/25000000000000000000)
  directionLo := (29264345386087900183/12500000000000000000)
  directionHi := (46822952617740640293/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree023.table
  base := (-8242967095813544385914165362567968829667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-86485551674572491144833290428900564000000000000000)
      constant := (593369826501684401304852493045001931558466361543888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree023.table
  base := (-4123702809797682795803045658191893256809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-10813071140496867734287686683533743000000000000000)
      constant := (74204515648459924921934669897994863153930469734044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29264345386087900183/12500000000000000000)
  centralHi := (46822952617740640293/20000000000000000000)
  directionLo := (119688212984338804363/50000000000000000000)
  directionHi := (239376425968677608727/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree024.table
  base := (-4536337380609025352194171264859828792637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-29882458758437141852005730062197787200000000000000)
      constant := (212763000885023764548715008112971445246578635937312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree024.table
  base := (-9076766772224214990264337414933073483727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-3736134190430836241477594650790783400000000000000)
      constant := (26607436832586654856058842794358157734686041580822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/50000000000000000000)
  centralHi := (239376425968677608727/100000000000000000000)
  directionLo := (244524895098629899627/100000000000000000000)
  directionHi := (61131223774657474907/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree025.table
  base := (-1224326675231758790910658742624296107149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-92809200876050359967201089944286159200000000000000)
      constant := (685101388062100914661378941503623772461470715695488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree025.table
  base := (-2449595438872805962384467138607906173897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-11603734002088149714577881221210957400000000000000)
      constant := (85676860098916376954016425593951697416586206581304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/100000000000000000000)
  centralHi := (61131223774657474907/25000000000000000000)
  directionLo := (249567175999677733207/100000000000000000000)
  directionHi := (31195896999959716651/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree026.table
  base := (-5208922008023121515623154071549785842033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-95971025476789294378384989701978956800000000000000)
      constant := (733788506764240935631957840385821579382145559929824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree026.table
  base := (-10421310776793925568865678814966558631567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-11999065432883790704722978490049564600000000000000)
      constant := (91765855158706527863308749626073939407714845813186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249567175999677733207/100000000000000000000)
  centralHi := (31195896999959716651/12500000000000000000)
  directionLo := (63627395018730083967/25000000000000000000)
  directionHi := (254509580074920335869/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree027.table
  base := (-10950293456691541365816352876027045857467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-33044283359176076263189629819890584800000000000000)
      constant := (261444731799484140516577910350417396465200833667696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree027.table
  base := (-5476739894570056591025246706719584858349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-4131465621226477231622691919629390600000000000000)
      constant := (32695758495372347319297151016089095813551245188228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63627395018730083967/25000000000000000000)
  centralHi := (254509580074920335869/100000000000000000000)
  directionLo := (129678908619877784753/50000000000000000000)
  directionHi := (259357817239755569507/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree028.table
  base := (-11398905499415277342926564477189710067267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-102294674678267163200752789217364552000000000000000)
      constant := (836724295159500612592305377968799193495655699310288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree028.table
  base := (-11401831588127149745288446449991211890019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-12789728294475072685013173027726779000000000000000)
      constant := (104639351480286079134822848252447678640205387842202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129678908619877784753/50000000000000000000)
  centralHi := (259357817239755569507/100000000000000000000)
  directionLo := (264117073239933915791/100000000000000000000)
  directionHi := (16507317077495869737/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree029.table
  base := (-5884884759347775374195806726929455957601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-105456499279006097611936688975057349600000000000000)
      constant := (890946389421058666873368847801494558112946145564128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree029.table
  base := (-11772454515790048989567770280933850928309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-13185059725270713675158270296565386200000000000000)
      constant := (111420531326075018623836884909435695174618078164022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264117073239933915791/100000000000000000000)
  centralHi := (16507317077495869737/6250000000000000000)
  directionLo := (268792074641881472689/100000000000000000000)
  directionHi := (26879207464188147269/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree030.table
  base := (-6034115417219426561326676825077544327403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-36206107959915010674373529577583382400000000000000)
      constant := (315663192910646915545974484898022598785022290133728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree030.table
  base := (-6035346415814363232638259934463403038757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-4526797052022118221767789188467997800000000000000)
      constant := (39476484287455094850235850429961810463873047960804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268792074641881472689/100000000000000000000)
  centralHi := (26879207464188147269/10000000000000000000)
  directionLo := (68346785953942699777/25000000000000000000)
  directionHi := (273387143815770799109/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree031.table
  base := (-12298985783156272088569654873723537263329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-111780148480483966434304488490442944800000000000000)
      constant := (1004844286959857238445628697924818203017578795465456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree031.table
  base := (-12301241804230098892231449892661330091867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-13975722586861995655448464834242600600000000000000)
      constant := (125664919344816436540487291278724328210418799580586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68346785953942699777/25000000000000000000)
  centralHi := (273387143815770799109/100000000000000000000)
  directionLo := (277906245732626726711/100000000000000000000)
  directionHi := (34738280716578340839/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree032.table
  base := (-498646556002125112712685410998540053561/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-114941973081222900845488388248135742400000000000000)
      constant := (1064502093716846717496957388098176396317905877487600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree032.table
  base := (-6234114954901221846253438214061811976777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-14371054017657636645593562103081207800000000000000)
      constant := (133125878494853684218257885244435519574654089768732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277906245732626726711/100000000000000000000)
  centralHi := (34738280716578340839/12500000000000000000)
  directionLo := (282353028017517948511/100000000000000000000)
  directionHi := (8823532125547435891/3125000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree033.table
  base := (-3143349783182369269918656050355911348447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-39367932560653945085557429335276180000000000000000)
      constant := (375318529716653005080699227950575248475138737751744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree033.table
  base := (-157191125733387984069707959805843122321/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-4922128482817759211912886457306605000000000000000)
      constant := (46937134781747335851233797671416266716214544520480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282353028017517948511/100000000000000000000)
  centralHi := (8823532125547435891/3125000000000000000)
  directionLo := (286730855409946141493/100000000000000000000)
  directionHi := (143365427704973070747/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree034.table
  base := (-3155972916570980093131859284747415237301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-121265622282700769667856187763521337600000000000000)
      constant := (1189198247875890976761280262792088225385746216011456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree034.table
  base := (-197275334843956858540844085024633375879/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-15161716879248918625883756640758422200000000000000)
      constant := (148720681479460779258329472673501765414158787589248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286730855409946141493/100000000000000000000)
  centralHi := (143365427704973070747/50000000000000000000)
  directionLo := (72760709889325573661/25000000000000000000)
  directionHi := (58208567911460458929/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree035.table
  base := (-2524092335836127710453915895895478396457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-124427446883439704079040087521214135200000000000000)
      constant := (1254224319369315135617797703128620442465630312712240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree035.table
  base := (-12622043234701618372742670089733638082113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-15557048310044559616028853909597029400000000000000)
      constant := (156852991328466758192287490847823208855903992772254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72760709889325573661/25000000000000000000)
  centralHi := (58208567911460458929/20000000000000000000)
  directionLo := (295291864891391429273/100000000000000000000)
  directionHi := (147645932445695714637/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree036.table
  base := (-12565596143392396267931558949675035848951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-42529757161392879496741329092968977600000000000000)
      constant := (440342910844792398617496779859885383870294177629488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree036.table
  base := (-1256704152024543019087490911193073536043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-5317459913613400202057983726145212200000000000000)
      constant := (55069233413636076460049013067139759226012211723980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295291864891391429273/100000000000000000000)
  centralHi := (147645932445695714637/50000000000000000000)
  directionLo := (37435076399951659981/12500000000000000000)
  directionHi := (299480611199613279849/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree037.table
  base := (-778843100963177835734784435671916816531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-130751096084917572901407887036599730400000000000000)
      constant := (1389607012529201692891720771544499748537447722585344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree037.table
  base := (-12462809964845089396454929815040403729037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-16347711171635841596319048447274243800000000000000)
      constant := (173784249085412301962206886112764334244634905709446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/12500000000000000000)
  centralHi := (299480611199613279849/100000000000000000000)
  directionLo := (303611573392636170647/100000000000000000000)
  directionHi := (37951446674079521331/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree038.table
  base := (-12310079826847639658020246201304038988451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-133912920685656507312591786794292528000000000000000)
      constant := (1459955208194366563681602357249432136705896050016464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree038.table
  base := (-12311285469645983687577829936461195588571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-16743042602431482586464145716112851000000000000000)
      constant := (182582144178722986237707175465262918353428043087018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303611573392636170647/100000000000000000000)
  centralHi := (37951446674079521331/12500000000000000000)
  directionLo := (307687078882767296473/100000000000000000000)
  directionHi := (153843539441383648237/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree039.table
  base := (-1514134846001112080116089714562038814419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-45691581762131813907925228850661775200000000000000)
      constant := (510689942890498342092097506577427445775854652104576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree039.table
  base := (-3028544810719553750275490621957589358917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-5712791344409041192203080994983819400000000000000)
      constant := (63866983120960366129670452773399689072283206952648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307687078882767296473/100000000000000000000)
  centralHi := (153843539441383648237/50000000000000000000)
  directionLo := (62341860583357128307/20000000000000000000)
  directionHi := (4870457858074775649/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree040.table
  base := (-11871999860475408575572027783343194450361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-140236569887134376134959586309678123200000000000000)
      constant := (1605947787996616354445812098556359305347955762574704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree040.table
  base := (-11873003972165604409277561028663056711969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-17533705464022764566754340253790065400000000000000)
      constant := (200840279079463483149560593362713066912234823470302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62341860583357128307/20000000000000000000)
  centralHi := (4870457858074775649/1562500000000000000)
  directionLo := (315680282150036406921/100000000000000000000)
  directionHi := (157840141075018203461/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree041.table
  base := (-5794090866027590026005334678681637020887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-143398394487873310546143486067370920800000000000000)
      constant := (1681586356621508068175244442453485863280224062427936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree041.table
  base := (-5794548799287617724854562329815580449211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-17929036894818405556899437522628672600000000000000)
      constant := (210299792309980945541222124469139407612218747640276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315680282150036406921/100000000000000000000)
  centralHi := (157840141075018203461/50000000000000000000)
  directionLo := (319601926702241204401/100000000000000000000)
  directionHi := (159800963351120602201/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree042.table
  base := (-11262809036980659440303048728342955890843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-48853406362870748319109128608354572800000000000000)
      constant := (586327706319991430179747374973720156122053643241584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree042.table
  base := (-11263644135445338558191121077788159239061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-6108122775204682182348178263822426600000000000000)
      constant := (73326395756504022938541224008694120513855909032146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319601926702241204401/100000000000000000000)
  centralHi := (159800963351120602201/50000000000000000000)
  directionLo := (40434503862195721163/12500000000000000000)
  directionHi := (64695206179513153861/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree043.table
  base := (-10896930703925948618612850243164740326673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-149722043689351179368511285582756516000000000000000)
      constant := (1838135936178964652631210960037293561402180096165872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree043.table
  base := (-10897691914699422490721089118295459323589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-18719699756409687537189632060305887000000000000000)
      constant := (229878196756027163349722947590722852572816373322262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40434503862195721163/12500000000000000000)
  centralHi := (64695206179513153861/20000000000000000000)
  directionLo := (163652141430154442927/50000000000000000000)
  directionHi := (65460856572061777171/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree044.table
  base := (-2098295188545595854944587155165330596511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-152883868290090113779695185340449313600000000000000)
      constant := (1919042913559840006670924627242601642585024069341520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree044.table
  base := (-10492169591636140201284260163883546430751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-19115031187205328527334729329144494200000000000000)
      constant := (239996584071038739060105909365156668351981942775458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163652141430154442927/50000000000000000000)
  centralHi := (65460856572061777171/20000000000000000000)
  directionLo := (331088273111808135463/100000000000000000000)
  directionHi := (41386034138976016933/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree045.table
  base := (-1004726829630395574252472499370244698637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-52015230963609682730293028366047370400000000000000)
      constant := (667234123948536238633440165532311303043054084966560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree045.table
  base := (-10047900194770450772489363948823493017087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-6503454206000323172493275532661033800000000000000)
      constant := (83444713146178416811097238339652315426246369153782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331088273111808135463/100000000000000000000)
  centralHi := (41386034138976016933/12500000000000000000)
  directionLo := (167414751146380033401/50000000000000000000)
  directionHi := (334829502292760066803/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree046.table
  base := (-4782518993039689709335118934946561774937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-159207517491567982602062984855834908800000000000000)
      constant := (2086112822067804657340567244370780430137810209306336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree046.table
  base := (-9565613469105534561165295965369035581813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-19905694048796610507624923866821708600000000000000)
      constant := (260890676858890402560257170195557966558301262684854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167414751146380033401/50000000000000000000)
  centralHi := (334829502292760066803/100000000000000000000)
  directionLo := (67705877623460604159/20000000000000000000)
  directionHi := (84632347029325755199/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree047.table
  base := (-452271638318296751016399430088943844503/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-162369342092306917013246884613527706400000000000000)
      constant := (2172272943413712384456810306362153586950344061099840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree047.table
  base := (-9045956728325195046622435268946225087529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-20301025479592251497770021135660315800000000000000)
      constant := (271666031342823339384065461419139650715273892216782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67705877623460604159/20000000000000000000)
  centralHi := (84632347029325755199/25000000000000000000)
  directionLo := (171094635825128769989/50000000000000000000)
  directionHi := (342189271650257539979/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree048.table
  base := (-8489027474787957744912966765659235388357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-55177055564348617141476928123740168000000000000000)
      constant := (753393854584144374794097085978069753463524043888016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree048.table
  base := (-8489504403044065377403071208414564671889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-6898785636795964162638372801499641000000000000000)
      constant := (94220018825903861759367364038273496453107733264554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171094635825128769989/50000000000000000000)
  centralHi := (342189271650257539979/100000000000000000000)
  directionLo := (345810422986340759341/100000000000000000000)
  directionHi := (172905211493170379671/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree049.table
  base := (-1579266488279794563078910489599992558373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-168692991293784785835614684128913301600000000000000)
      constant := (2349837642488155144863776788132606515316781087573360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree049.table
  base := (-7896766447786184112701625732170839105161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-21091688341183533478060215673337530200000000000000)
      constant := (293872622284794771632274290946961542965184006420238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345810422986340759341/100000000000000000000)
  centralHi := (172905211493170379671/50000000000000000000)
  directionLo := (349394046399548826489/100000000000000000000)
  directionHi := (34939404639954882649/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree050.table
  base := (-7267800898002554049174457113419871919791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-171854815894523720246798583886606099200000000000000)
      constant := (2441240255452071837572859690924478804674666319326224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree050.table
  base := (-7268195748227638032328802434796846450949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-21487019771979174468205312942176137400000000000000)
      constant := (305303613331194099221487921599215468124575215093142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349394046399548826489/100000000000000000000)
  centralHi := (34939404639954882649/10000000000000000000)
  directionLo := (352941285021897435639/100000000000000000000)
  directionHi := (8823532125547435891/2500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree051.table
  base := (-6603835510923221178079020098677160034531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-58338880165087551552660827881432965600000000000000)
      constant := (844796193860547188707348197874269531523607769804528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree051.table
  base := (-1320838930392874607019494124571947655909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-7294117067591605152783470070338248200000000000000)
      constant := (105650975688443457322728711917991999555995241341370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352941285021897435639/100000000000000000000)
  centralHi := (8823532125547435891/2500000000000000000)
  directionLo := (356453225103051084751/100000000000000000000)
  directionHi := (22278326568940692797/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree052.table
  base := (-2952397072330633558202228533025397419867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-178178465096001589069166383401991694400000000000000)
      constant := (2629281891168124662768236578330878221477845564873376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree052.table
  base := (-590512073024963672964255359260573460467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-22277682633570456448495507479853351800000000000000)
      constant := (328820472348354830369500838694059230857317042993860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356453225103051084751/100000000000000000000)
  centralHi := (22278326568940692797/6250000000000000000)
  directionLo := (89982724973958394813/25000000000000000000)
  directionHi := (359930899895833579253/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree053.table
  base := (-5170994950166870081334413659225077671019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2423147853)
      previous := (0)
      next := (2155128675)
      square := (56357797881349640024031267974649600000000000000)
      linear := (-3421514899938500443025477040748764000000000000000)
      constant := (51432444065684248199923253034984703073569721062672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree053.table
  base := (-2585645932221596637858598084191340587209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (302972691)
      previous := (0)
      next := (269311875)
      square := (7044724735168705003003908496831200000000000000)
      linear := (-427792718195586744125294429220603000000000000000)
      constant := (6432191852032066087547010847123940190606569954348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/25000000000000000000)
  centralHi := (359930899895833579253/100000000000000000000)
  directionLo := (363375293207013095813/100000000000000000000)
  directionHi := (181687646603506547907/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree054.table
  base := (-4402720859589930308812894720160374108999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-61500704765826485963844727639125763200000000000000)
      constant := (941433645868068890742686895208829673684640787480112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree054.table
  base := (-2201495369516287782234821662385661642521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-7689448498387246142928567339176855400000000000000)
      constant := (117736647480627426728429141604140814455581020647412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363375293207013095813/100000000000000000000)
  centralHi := (181687646603506547907/50000000000000000000)
  directionLo := (366787342647944849441/100000000000000000000)
  directionHi := (183393671323972424721/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree055.table
  base := (-3600223559051383508734971911650655555269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-187663938898218392302718082675070087200000000000000)
      constant := (2924425584332756149475625519718010090741230705213616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree055.table
  base := (-56257325199588413867931431763534285333/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-23463676925957379418930799286369173400000000000000)
      constant := (365731731108330528077633798046625686727713854528896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366787342647944849441/100000000000000000000)
  centralHi := (183393671323972424721/50000000000000000000)
  directionLo := (370167942615509409891/100000000000000000000)
  directionHi := (92541985653877352473/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree056.table
  base := (-2763727002023878008862896217505250959071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-190825763498957326713901982432762884800000000000000)
      constant := (3026293019011374585782016868460585955876628528208144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree056.table
  base := (-2763949830538214319620371599375324724531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-23859008356753020409075896555207780600000000000000)
      constant := (378471477128270697099731731389507935934473726696698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370167942615509409891/100000000000000000000)
  centralHi := (92541985653877352473/25000000000000000000)
  directionLo := (14940717881208103841/4000000000000000000)
  directionHi := (186758973515101298013/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree057.table
  base := (-189343051811992439472189163546587039819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-64662529366565420375028627396818560800000000000000)
      constant := (1043300945064719334037622589924003383633617550682720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree057.table
  base := (-946816465332502829677547171885650340543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-8084779929182887133073664608015462600000000000000)
      constant := (130476376581572408204639037040201157610036042818796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14940717881208103841/4000000000000000000)
  centralHi := (186758973515101298013/50000000000000000000)
  directionLo := (188419085927564273641/50000000000000000000)
  directionHi := (376838171855128547283/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree058.table
  base := (-494755782652681483740437202773084158309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-197149412700435195536269781948148480000000000000000)
      constant := (3235254671032897114403793187435499616884131080064352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree058.table
  base := (-494847697914862147741791141111512694947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-24649671218344302389366091092884995000000000000000)
      constant := (404604643771322436397623554117936217366180581222452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188419085927564273641/50000000000000000000)
  centralHi := (376838171855128547283/100000000000000000000)
  directionLo := (4751617467711875801/1250000000000000000)
  directionHi := (380129397416950064081/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree059.table
  base := (-13032041912252850354623367391474427879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-200311237301174129947453681705841277600000000000000)
      constant := (3342348204306348966925485063867525556549623707906624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree059.table
  base := (-26147544770695836998365564644436208871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-25045002649139943379511188361723602200000000000000)
      constant := (417997978971354932270253662177474767601416024268836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751617467711875801/1250000000000000000)
  centralHi := (380129397416950064081/100000000000000000000)
  directionLo := (191696185273750118327/50000000000000000000)
  directionHi := (76678474109500047331/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree060.table
  base := (918578924431492786640249594952741975999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-67824353967304354786212527154511358400000000000000)
      constant := (1150394382671785559304003312799406237922889909623888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree060.table
  base := (28700855774328242681363593634114600159/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-8480111359978528123218761876854069800000000000000)
      constant := (143869699835795642550076784670561944285494822439232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191696185273750118327/50000000000000000000)
  centralHi := (76678474109500047331/20000000000000000000)
  directionLo := (193313903281353441673/50000000000000000000)
  directionHi := (386627806562706883347/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree061.table
  base := (961242159481586572606295783715545794763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-206634886502651998769821481221226872800000000000000)
      constant := (3561759246477620130405381474225764643372752017744736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree061.table
  base := (48058669241842783899022682026778324437/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-25835665510731225359801382899400816600000000000000)
      constant := (445437973453416940185390317242193913891686619894160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/50000000000000000000)
  centralHi := (386627806562706883347/100000000000000000000)
  directionLo := (389836391093684398527/100000000000000000000)
  directionHi := (6091193610838818727/1562500000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree062.table
  base := (591895256742620377283592113668507330327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-209796711103390933181005380978919670400000000000000)
      constant := (3674076271863927979708469024203336137218121784589360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree062.table
  base := (1479675727977298238799921591509421525591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-26230996941526866349946480168239423800000000000000)
      constant := (459484572362155200649206119431398417660205829855644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389836391093684398527/100000000000000000000)
  centralHi := (6091193610838818727/1562500000000000000)
  directionLo := (49127347722908848389/12500000000000000000)
  directionHi := (393018781783270787113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree063.table
  base := (2014727619440876509741879696156786870527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-70986178568043289197396426912204156000000000000000)
      constant := (1262711340374887475447927706761120938973029770150048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree063.table
  base := (805868395264716480782462414514558509927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-8875442790774169113363859145692677000000000000000)
      constant := (157916290293691441055440167098034401743828634929890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49127347722908848389/12500000000000000000)
  centralHi := (393018781783270787113/100000000000000000000)
  directionLo := (198087804929950436843/50000000000000000000)
  directionHi := (396175609859900873687/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree064.table
  base := (5132332419094882754269117744034898438197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-216120360304868802003373180494305265600000000000000)
      constant := (3903932313261514578105878045430677691744709602842192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree064.table
  base := (2566114834114775805531258839958240252787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-27021659803118148330236674705916638200000000000000)
      constant := (488230846411593567421758687568565194057194399076108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198087804929950436843/50000000000000000000)
  centralHi := (396175609859900873687/100000000000000000000)
  directionLo := (399307481599484373131/100000000000000000000)
  directionHi := (99826870399871093283/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree065.table
  base := (1253605737045168413181557874387414066143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-219282184905607736414557080251998063200000000000000)
      constant := (4021470986904713702780959859743511831722684681880240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree065.table
  base := (1566983871621846936280957914142679131909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-27416991233913789320381771974755245400000000000000)
      constant := (502930478806435695506107910576520572016683540748712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399307481599484373131/100000000000000000000)
  centralHi := (99826870399871093283/25000000000000000000)
  directionLo := (402414979684877928737/100000000000000000000)
  directionHi := (201207489842438964369/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree066.table
  base := (7436473468886662490120715994463576062921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-74148003168782223608580326669896953600000000000000)
      constant := (1380249966053592214954008148509425967966975167695152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree066.table
  base := (1859097237126293092452183890547695710747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-9270774221569810103508956414531284200000000000000)
      constant := (172615916700261090401237108143754393971794063269832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402414979684877928737/100000000000000000000)
  centralHi := (201207489842438964369/50000000000000000000)
  directionLo := (405498664471584765481/100000000000000000000)
  directionHi := (202749332235792382741/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree067.table
  base := (539850239653096291874876727368769904537/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-225605834107085605236924879767383658400000000000000)
      constant := (4261768918699909286753975807755178235295504340678912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree067.table
  base := (8637527196984698791336942529739404795401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-28207654095505071300671966512432459800000000000000)
      constant := (532982644273376915691313447136489913661521194489842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405498664471584765481/100000000000000000000)
  centralHi := (202749332235792382741/50000000000000000000)
  directionLo := (408559075167468340763/100000000000000000000)
  directionHi := (102139768791867085191/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree068.table
  base := (1233920455654580765632603512255050800101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-228767658707824539648108779525076456000000000000000)
      constant := (4384527934055813922802215684973568780978833714383488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree068.table
  base := (1974258833347420937571200764041616208519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-28602985526300712290817063781271067000000000000000)
      constant := (548335147034150741435801343482453216369119145173990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408559075167468340763/100000000000000000000)
  centralHi := (102139768791867085191/25000000000000000000)
  directionLo := (411596730933513623647/100000000000000000000)
  directionHi := (12862397841672300739/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree069.table
  base := (2784425705519211155917449543602788772617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-77309827769521158019764226427589751200000000000000)
      constant := (1503008947371279572251446526195481885040179384116416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree069.table
  base := (2784409960953979542508581147956073724703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-9666105652365451093654053683369891400000000000000)
      constant := (187968415211799309752284896409723534104438094915368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411596730933513623647/100000000000000000000)
  centralHi := (12862397841672300739/3125000000000000000)
  directionLo := (25913258244499976391/6250000000000000000)
  directionHi := (414612131911999622257/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree070.table
  base := (12436576683800174608953705924927229267331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-235091307909302408470476579040462051200000000000000)
      constant := (4635265551766203509245240323796318633094310052007216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree070.table
  base := (12436519606541872554332044626510931515429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-29393648387891994271107258318948281400000000000000)
      constant := (579692928703809128513843593476003793070906213455018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25913258244499976391/6250000000000000000)
  centralHi := (414612131911999622257/100000000000000000000)
  directionLo := (26100360011740584317/6250000000000000000)
  directionHi := (417605760187849349073/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree071.table
  base := (6883972680224184274679410866708884839927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 287192160000000000000000000000000000000000000000
      center := (1808828679)
      previous := (0)
      next := (1608758025)
      square := (42069905460725787623572636657132800000000000000)
      linear := (-3355677922676638632136063081664152800000000000000)
      constant := (67087943404443638297788450082747418970673977874464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree071.table
  base := (2753578727840222096920642964282210242277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35899020000000000000000000000000000000000000000
      center := (226162713)
      previous := (0)
      next := (201035625)
      square := (5258738182590723452946579582141600000000000000)
      linear := (-419563096037854017764117684335026600000000000000)
      constant := (8390115297056817913271542243938583675565853434270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26100360011740584317/6250000000000000000)
  centralHi := (417605760187849349073/100000000000000000000)
  directionLo := (420578080688389781029/100000000000000000000)
  directionHi := (42057808068838978103/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree072.table
  base := (15131773271042920079024593941838387873759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-80471652370260092430948126185282548800000000000000)
      constant := (1630987353136606278044794418662495338863038949053008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree072.table
  base := (15131726410261416984837719369860187447207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-10061437083161092083799150952208498600000000000000)
      constant := (203973669580229247122692997140167540963744778187898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420578080688389781029/100000000000000000000)
  centralHi := (42057808068838978103/10000000000000000000)
  directionLo := (423529542026276922767/100000000000000000000)
  directionHi := (26470596376642307673/6250000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree073.table
  base := (2066003582336129916464738971618757988847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-244576781711519211704028278313540444000000000000000)
      constant := (5024419720094813466099000077285371116004384027684736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree073.table
  base := (16527986207887774342799796506680568223029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-30579642680278917241542550125464103000000000000000)
      constant := (628361388569961160374623538198697538650974165974218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423529542026276922767/100000000000000000000)
  centralHi := (26470596376642307673/6250000000000000000)
  directionLo := (213230288644956602817/50000000000000000000)
  directionHi := (85292115457982641127/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree074.table
  base := (3591336635323976841731690076455889053219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-247738606312258146115212178071233241600000000000000)
      constant := (5157616905969600906405864070279861685327958344487920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree074.table
  base := (17956644726364392775053344964043835035883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-30974974111074558231687647394302710200000000000000)
      constant := (645019318364207382374478424950460039495292038196086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213230288644956602817/50000000000000000000)
  centralHi := (85292115457982641127/20000000000000000000)
  directionLo := (429371604785300398253/100000000000000000000)
  directionHi := (214685802392650199127/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree075.table
  base := (19417711519514278944044726022418495434667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-83633476970999026842132025942975346400000000000000)
      constant := (1764184521811667744841780647001911454960869432578704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree075.table
  base := (19417676697759015651621983532716130041809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-10456768513956733073944248221047105800000000000000)
      constant := (220631597227686322915956867748342987082507955034326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429371604785300398253/100000000000000000000)
  centralHi := (214685802392650199127/50000000000000000000)
  directionLo := (432263028732925949177/100000000000000000000)
  directionHi := (216131514366462974589/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree076.table
  base := (20911091095064577665019840019688033541921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-254062255513736014937579977586618836800000000000000)
      constant := (5429229652423851661817973596945924235041302872029456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree076.table
  base := (10455529781904286098682407650575306836913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-31765636972665840211977841931979924600000000000000)
      constant := (678987802776797205779370863298980840513351566658692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432263028732925949177/100000000000000000000)
  centralHi := (216131514366462974589/50000000000000000000)
  directionLo := (217567619961484922237/50000000000000000000)
  directionHi := (17405409596918793779/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree077.table
  base := (22436801731339743723106265428632426887911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-257224080114474949348763877344311634400000000000000)
      constant := (5567645125804281023202339544208473697895266789642096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree077.table
  base := (11218386591786749417488440206956517892673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-32160968403461481202122939200818531800000000000000)
      constant := (696298346511838148766243314782674715384423847502532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/50000000000000000000)
  centralHi := (17405409596918793779/4000000000000000000)
  directionLo := (218994308165919402763/50000000000000000000)
  directionHi := (437988616331838805527/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree078.table
  base := (11997412707995568516513364075890152497693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-86795301571737961253315925700668144000000000000000)
      constant := (1902599982949317866360816964836644098041098079051232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree078.table
  base := (11997399786455157402585352826995212330293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-10852099944752374064089345489885713000000000000000)
      constant := (237942139434776199856030765590021597825453992394204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218994308165919402763/50000000000000000000)
  centralHi := (437988616331838805527/100000000000000000000)
  directionLo := (44082352370278160929/10000000000000000000)
  directionHi := (440823523702781609291/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree079.table
  base := (25585146063792841520804446029035146501309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-263547729315952818171131676859697229600000000000000)
      constant := (5849694088756058887488932453655606164696354359215824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree079.table
  base := (25585122672256228686561659663918490130097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-32951631265052763182413133738495746200000000000000)
      constant := (731572014060958340717423790568711987104406099115074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44082352370278160929/10000000000000000000)
  centralHi := (440823523702781609291/100000000000000000000)
  directionLo := (110910079023277632009/25000000000000000000)
  directionHi := (443640316093110528037/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree080.table
  base := (27207749309401548975394871317004479316523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-266709553916691752582315576617390027200000000000000)
      constant := (5993327516236737674252387323034694440126571704823728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree080.table
  base := (5441545627922519191217151728231927038687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-33346962695848404172558231007334353400000000000000)
      constant := (749535130126195129338322608826386786225712971229270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110910079023277632009/25000000000000000000)
  centralHi := (443640316093110528037/100000000000000000000)
  directionLo := (55804917048793344467/12500000000000000000)
  directionHi := (446439336390346755737/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree081.table
  base := (3607827790321139176006678311909251113071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-89957126172476895664499825458360941600000000000000)
      constant := (2046233401709429514285681659070644340160017012095616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree081.table
  base := (28862603165962013036993867300983954074131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-11247431375548015054234442758724320200000000000000)
      constant := (255905254411745881525401750490282565435867600928834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/12500000000000000000)
  centralHi := (446439336390346755737/100000000000000000000)
  directionLo := (112305229199854979943/25000000000000000000)
  directionHi := (449220916799419919773/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree082.table
  base := (30549753643349224399978287882320556335967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-273033203118169621404683376132775622400000000000000)
      constant := (6285812132063143679253141393666567769444349143772912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree082.table
  base := (15274868155331021595330438046695236399463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-34137625557439686152848425545011567800000000000000)
      constant := (786113910472060139720838391682407218000808513212892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112305229199854979943/25000000000000000000)
  centralHi := (449220916799419919773/100000000000000000000)
  directionLo := (903970758605762687/200000000000000000)
  directionHi := (451985379302881343501/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree083.table
  base := (32269133035112890965928432270221643434027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-276195027718908555815867275890468420000000000000000)
      constant := (6434663276168157987059006099611175649116633024561072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree083.table
  base := (1613455867731584800868453184915642531847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-34532956988235327142993522813850175000000000000000)
      constant := (804729569231992165494769180709698586738034904771480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (903970758605762687/200000000000000000)
  centralHi := (451985379302881343501/100000000000000000000)
  directionLo := (454733036095935835651/100000000000000000000)
  directionHi := (113683259023983958913/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree084.table
  base := (6804150270685936641955019492954415702257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-93118950773215830075683725216053739200000000000000)
      constant := (2195084539599083167880098250530575915753651072343920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree084.table
  base := (272165897355111432068312032418222215077/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-11642762806343656044379540027562927400000000000000)
      constant := (274520912396112816687012527779683213333783501009750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454733036095935835651/100000000000000000000)
  centralHi := (113683259023983958913/25000000000000000000)
  directionLo := (457464189997955849271/100000000000000000000)
  directionHi := (57183023749744481159/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree085.table
  base := (3580460042908655525881480238219093314713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-282518676920386424638235075405854015200000000000000)
      constant := (6737583143292867253972045685427235744697873023755680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree085.table
  base := (895114690005305350014880313881961382807/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-35323619849826609123283717351527389400000000000000)
      constant := (842613412262598763658422806458986492347054986355760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457464189997955849271/100000000000000000000)
  centralHi := (57183023749744481159/12500000000000000000)
  directionLo := (460179134842013467563/100000000000000000000)
  directionHi := (115044783710503366891/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree086.table
  base := (37620672963706743481072142793918383423197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-285680501521125359049418975163546812800000000000000)
      constant := (6891651834773151468641196025126059711833014597802192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree086.table
  base := (37620661361889787037964919154109422242799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-35718951280622250113428814620365996600000000000000)
      constant := (861881592597896170275742509585981633342107071714558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460179134842013467563/100000000000000000000)
  centralHi := (115044783710503366891/25000000000000000000)
  directionLo := (462878155843848585271/100000000000000000000)
  directionHi := (57859769480481073159/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree087.table
  base := (39468962436600492932019244384422199263069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-96280775373954764486867624973746536800000000000000)
      constant := (2349153226647332074073259774604502489153003159935728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree087.table
  base := (7893790389137874167594842543856268137739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-12038094237139297034524637296401534600000000000000)
      constant := (293789092178421729171867090785771054956190985536730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462878155843848585271/100000000000000000000)
  centralHi := (57859769480481073159/12500000000000000000)
  directionLo := (232780764975792374357/50000000000000000000)
  directionHi := (93112305990316949743/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree088.table
  base := (4134946302162967388073203876656939211023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-292004150722603227871786774678932408000000000000000)
      constant := (7205006666919531037763727037317351093321169773757280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree088.table
  base := (10337363384082846488244189632523526116793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-36509614142213532093719009158043211000000000000000)
      constant := (901070462592489666087902317239218823492858588497224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232780764975792374357/50000000000000000000)
  centralHi := (93112305990316949743/20000000000000000000)
  directionLo := (468229526177406402929/100000000000000000000)
  directionHi := (46822952617740640293/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree089.table
  base := (43262169513001879135724235382900456822221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-295165975323342162282970674436625205600000000000000)
      constant := (7364292785090810277149289547728941353719298733410256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree089.table
  base := (43262160937882119501687413233802284371973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-36904945573009173083864106426881818200000000000000)
      constant := (920991149445214215223109102024544775167277537781866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468229526177406402929/100000000000000000000)
  centralHi := (46822952617740640293/10000000000000000000)
  directionLo := (470882405912321885299/100000000000000000000)
  directionHi := (4708824059123218853/1000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree090.table
  base := (1808283090361130239131191513521755867099/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-99442599974693698898051524731439334400000000000000)
      constant := (2508439341656913699542992108377518291405836055677200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree090.table
  base := (22603534753800956449064037780232964751743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-12433425667934938024669734565240141800000000000000)
      constant := (313709778636694409175595369905408220683068687094804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470882405912321885299/100000000000000000000)
  centralHi := (4708824059123218853/1000000000000000000)
  directionLo := (236760211612527305191/50000000000000000000)
  directionHi := (473520423225054610383/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree091.table
  base := (47184182102984813521270910762879314440329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-301489624524820031105338473952010800800000000000000)
      constant := (7688082378083495857789256100907355657122404664006544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree091.table
  base := (47184175096888851710086822424635129035131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-37695608434600455064154300964559032600000000000000)
      constant := (961485020929688427001427462569568984928536714148502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236760211612527305191/50000000000000000000)
  centralHi := (473520423225054610383/100000000000000000000)
  directionLo := (238071912573014901277/50000000000000000000)
  directionHi := (95228765029205960511/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree092.table
  base := (49193480330310749652548186624170044792829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-304651449125558965516522373709703598400000000000000)
      constant := (7852585836854846099139691525458147723536580122446544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree092.table
  base := (12298368499638045927401923943085713859881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-38090939865396096054299398233397639800000000000000)
      constant := (982058203559129757444903468553758227661392124152008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238071912573014901277/50000000000000000000)
  centralHi := (95228765029205960511/20000000000000000000)
  directionLo := (119688212984338804363/25000000000000000000)
  directionHi := (478752851937355217453/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree093.table
  base := (6404371077682597539655725185561992903939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-102604424575432633309235424489132132000000000000000)
      constant := (2672942798172008474075672083439841973651685570185344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree093.table
  base := (51234962899733073942309918973245049420481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-12828757098730579014814831834078749000000000000000)
      constant := (334282960984671893762488541364975928969244178127734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/25000000000000000000)
  centralHi := (478752851937355217453/100000000000000000000)
  directionLo := (120336934337407745289/25000000000000000000)
  directionHi := (481347737349630981157/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree094.table
  base := (53308644009802694007280158433695172839509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-310975098327036834338890173225089193600000000000000)
      constant := (8186810045017879886536288237325379451732398653651024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree094.table
  base := (5330863883986449420105837185851219030139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-38881602726987378034589592771074854200000000000000)
      constant := (1023857058359747868334779523659410840858101180028380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120336934337407745289/25000000000000000000)
  centralHi := (481347737349630981157/100000000000000000000)
  directionLo := (96785741773273091367/20000000000000000000)
  directionHi := (120982177216591364209/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree095.table
  base := (27707251922008713897822249958039830978659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-314136922927775768750074072982781991200000000000000)
      constant := (8356530782954199347496108235912906235007103088010848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree095.table
  base := (1385362479328201754736084552352141984151/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-39276934157783019024734690039913461400000000000000)
      constant := (1045082729101952082766681660284479293665452906693680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96785741773273091367/20000000000000000000)
  centralHi := (120982177216591364209/25000000000000000000)
  directionLo := (60811998492090057839/12500000000000000000)
  directionHi := (486495987936720462713/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree096.table
  base := (57552545754517781458901329312966198129499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-105766249176171567720419324246824929600000000000000)
      constant := (2842663534497747684696257871800609580326457106815888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree096.table
  base := (57552541534924486007132940265526462619691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-13224088529526220004959929102917356200000000000000)
      constant := (355508631525977352611792147533536093508002043726674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60811998492090057839/12500000000000000000)
  centralHi := (486495987936720462713/100000000000000000000)
  directionLo := (244524895098629899627/50000000000000000000)
  directionHi := (97809958039451959851/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree097.table
  base := (7465345952931782762975739058013917678691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-320460572129253637572441872498167586400000000000000)
      constant := (8701189502316579636339983583046193662217069802113408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree097.table
  base := (59722763811926381051584873431109383246309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-40067597019374301005024884577590675800000000000000)
      constant := (1088186554249036487128656968635120804736563073191978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/50000000000000000000)
  centralHi := (97809958039451959851/20000000000000000000)
  directionLo := (491590325683329524677/100000000000000000000)
  directionHi := (245795162841664762339/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree098.table
  base := (61925167557923200022280341251567058313121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-323622396729992571983625772255860384000000000000000)
      constant := (8876127475564456729864472945293208282018717351952656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree098.table
  base := (61925164115329285531277640653865065193689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-40462928450169941995169981846429283000000000000000)
      constant := (1110064707633841141642863122225474581474095771521938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491590325683329524677/100000000000000000000)
  centralHi := (245795162841664762339/50000000000000000000)
  directionLo := (98823559806131281979/20000000000000000000)
  directionHi := (61764724878832051237/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree099.table
  base := (32079871933016916321845428010218238040883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-108928073776910502131603224004517727200000000000000)
      constant := (3017601506595666740098872907304325573168948690165792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree099.table
  base := (32079870378478831346480462017499239379629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-13619419960321860995105026371755963400000000000000)
      constant := (377386784767352901713447886319385895143844021567612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98823559806131281979/20000000000000000000)
  centralHi := (61764724878832051237/12500000000000000000)
  directionLo := (99326481933542440639/20000000000000000000)
  directionHi := (124158102416928050799/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree100.table
  base := (66426495035528080952658061032724367455409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-329946045931470440805993571771245979200000000000000)
      constant := (9231220631900618591888290791546922506596483562193424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree100.table
  base := (2075827882122503808727538896220744308403/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-41253591311761223975460176384106497400000000000000)
      constant := (1154473493869098349922741944463016089610558169661632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99326481933542440639/20000000000000000000)
  centralHi := (124158102416928050799/25000000000000000000)
  directionLo := (249567175999677733207/50000000000000000000)
  directionHi := (99826870399871093283/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree101.table
  base := (17181354928669935393258889478618089015931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-333107870532209375217177471528938776800000000000000)
      constant := (9411375809149055151298506240155858726882432951747264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree101.table
  base := (68725417179540836427428568248700971251019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-41648922742556864965605273652945104600000000000000)
      constant := (1177004125991205478618376248920018994600814268319798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249567175999677733207/50000000000000000000)
  centralHi := (99826870399871093283/20000000000000000000)
  directionLo := (501623815582229559631/100000000000000000000)
  directionHi := (31351488473889347477/6250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree102.table
  base := (8882064586903653958335965951123948684459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-112089898377649436542787123762210524800000000000000)
      constant := (3197756683022863624843928355396669726374598571611264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree102.table
  base := (71056514406323587785088101738383364954779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-14014751391117501985250123640594570600000000000000)
      constant := (399917416787039849307711913915439154807290087985906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501623815582229559631/100000000000000000000)
  centralHi := (31351488473889347477/6250000000000000000)
  directionLo := (504100985292364625049/100000000000000000000)
  directionHi := (10082019705847292501/2000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree103.table
  base := (9177473112142030864204255606536869541399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-339431519733687244039545271044324372000000000000000)
      constant := (9776903349456954095606668248369030759382611011568512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree103.table
  base := (73419782830731055932344892208492702244891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-42439585604148146945895468190622319000000000000000)
      constant := (1222717866704194567841816999155374745282978047038422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504100985292364625049/100000000000000000000)
  centralHi := (10082019705847292501/2000000000000000000)
  directionLo := (20262641659416117933/4000000000000000000)
  directionHi := (253283020742701474163/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree104.table
  base := (75815223354956075155124850988563754337927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-342593344334426178450729170802017169600000000000000)
      constant := (9962275708345540933580463787375669852932732237871472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree104.table
  base := (37907610744792668058714857511187822199819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-42834917034943787936040565459460926200000000000000)
      constant := (1245900974774932824024102826289819289511289997138796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20262641659416117933/4000000000000000000)
  centralHi := (253283020742701474163/50000000000000000000)
  directionLo := (63627395018730083967/12500000000000000000)
  directionHi := (509019160149840671737/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree105.table
  base := (19560707801416540205298425493490308527031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-115251722978388370953971023519903322400000000000000)
      constant := (3383129041324864291408958318147799774497140805421888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree105.table
  base := (19560707380479123478172188854223850805373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-14410082821913142975395220909433177800000000000000)
      constant := (423100524784629226837510763306639427689636826912888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63627395018730083967/12500000000000000000)
  centralHi := (509019160149840671737/100000000000000000000)
  directionLo := (255730256526827164663/50000000000000000000)
  directionHi := (511460513053654329327/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree106.table
  base := (20175651919447028623837897950196282165241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 384729120000000000000000000000000000000000000000
      center := (2423147853)
      previous := (0)
      next := (2155128675)
      square := (56357797881349640024031267974649600000000000000)
      linear := (-6583339500677434854209376798441561600000000000000)
      constant := (195061086693792751843245644661996674285881945807168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree106.table
  base := (80702606158104550996345174480548569518473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (302972691)
      previous := (0)
      next := (269311875)
      square := (7044724735168705003003908496831200000000000000)
      linear := (-823124148991227734270391698059210200000000000000)
      constant := (24394710664998038793367487820731391853351261762922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255730256526827164663/50000000000000000000)
  centralHi := (511460513053654329327/100000000000000000000)
  directionLo := (513890267884657916363/100000000000000000000)
  directionHi := (128472566971164479091/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree107.table
  base := (4159727604083347685717905910602993065483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-352078818136642981684280870075095562400000000000000)
      constant := (10528827119328558975090397490066450288268633958285760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree107.table
  base := (83194550710176868554022712825145215254587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-44020911327330710906475857265976747800000000000000)
      constant := (1316755247272605391638161025700912837255833939013654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513890267884657916363/100000000000000000000)
  centralHi := (128472566971164479091/25000000000000000000)
  directionLo := (516308588384915054119/100000000000000000000)
  directionHi := (12907714709622876353/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree108.table
  base := (85718663800784164002799705516184306761769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-118413547579127305365154923277596120000000000000000)
      constant := (3573718565463367113690498117447432862506935605390128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree108.table
  base := (85718662563137682289159864265844746993079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-14805414252708783965540318178271785000000000000000)
      constant := (446936106760087898686854072229957168471105442822106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516308588384915054119/100000000000000000000)
  centralHi := (12907714709622876353/2500000000000000000)
  directionLo := (129678908619877784753/25000000000000000000)
  directionHi := (518715634479511139013/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree109.table
  base := (88274942283994377723516984117873653215807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-358402467338120850506648669590481157600000000000000)
      constant := (10915223324831822082534769495023380621401383765159152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree109.table
  base := (22068735291804934285147431322411002911349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-44811574188921992886766051803653962200000000000000)
      constant := (1365078884127744618953700311028525042485261957774632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129678908619877784753/25000000000000000000)
  centralHi := (518715634479511139013/100000000000000000000)
  directionLo := (260555781199986028087/50000000000000000000)
  directionHi := (20844462495998882247/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree110.table
  base := (90863387038587255697337175485619684149763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-361564291938859784917832569348173955200000000000000)
      constant := (11111030003649053118881508191424071533309366216152368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree110.table
  base := (90863386030959743933040236273490671269921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-45206905619717633876911149072492569400000000000000)
      constant := (1389566938689782502141256294982544495251899467579682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260555781199986028087/50000000000000000000)
  centralHi := (20844462495998882247/4000000000000000000)
  directionLo := (523496524802598985621/100000000000000000000)
  directionHi := (261748262401299492811/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree111.table
  base := (93483997624086676806001934829168363867353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-121575372179866239776338823035288917600000000000000)
      constant := (3769525243981211766893284470749390972892130179007536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree111.table
  base := (93483996715009888329784063390242622850853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-15200745683504424955685415447110392200000000000000)
      constant := (471424161284798346069677964460506127443428041644942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523496524802598985621/100000000000000000000)
  centralHi := (261748262401299492811/50000000000000000000)
  directionLo := (262935335440986468691/50000000000000000000)
  directionHi := (525870670881972937383/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree112.table
  base := (6008548352919295696577736908944887654807/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-367887941140337653740200368863559550400000000000000)
      constant := (11507860508912617901153376181940217934503098122610432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree112.table
  base := (48068386413303500864476938725460868614509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-45997568481308915857201343610169783800000000000000)
      constant := (1439195519521473555958230274481344565288856758512756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262935335440986468691/50000000000000000000)
  centralHi := (525870670881972937383/100000000000000000000)
  directionLo := (264117073239933915791/50000000000000000000)
  directionHi := (528234146479867831583/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree113.table
  base := (98821714754408394933246449522251199676043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-371049765741076588151384268621252348000000000000000)
      constant := (11708884333838158467642303051925633860867634034902448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree113.table
  base := (193011160184823000495922463123130549023/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-46392899912104556847346440879008391000000000000000)
      constant := (1464336045601523086373012742815597845567833532398592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264117073239933915791/50000000000000000000)
  centralHi := (528234146479867831583/100000000000000000000)
  directionLo := (26529354709489855471/5000000000000000000)
  directionHi := (530587094189797109421/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree114.table
  base := (101538820632452249150424469092187251116649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-124737196780605174187522722792981715200000000000000)
      constant := (3970549068692831770025484420180773255361945050576688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree114.table
  base := (101538819965178680502412692361658935086283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-15596077114300065945830512715948999400000000000000)
      constant := (496564687338178755955617516209545209247090781170962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26529354709489855471/5000000000000000000)
  centralHi := (530587094189797109421/100000000000000000000)
  directionLo := (266464826728702973469/50000000000000000000)
  directionHi := (532929653457405946939/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree115.table
  base := (104288090999461285769274580054581953209281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-377373414942554456973752068136637943200000000000000)
      constant := (12116149125059878528287887184444524266553265631302416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree115.table
  base := (104288090397631106146551338420232728275899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-47183562773695838827636635416685605400000000000000)
      constant := (1515269568688986850515508660129467715630920552404758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266464826728702973469/50000000000000000000)
  centralHi := (532929653457405946939/100000000000000000000)
  directionLo := (133815490169227269293/25000000000000000000)
  directionHi := (535261960676909077173/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree116.table
  base := (107069525603873811851277047896112569080713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-380535239543293391384935967894330740800000000000000)
      constant := (12322390090269357645901886192353942652653818183751568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree116.table
  base := (107069525061107834172367638724739364824019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-47578894204491479817781732685524212600000000000000)
      constant := (1541062565560930077755335358976659239963493757385798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133815490169227269293/25000000000000000000)
  centralHi := (535261960676909077173/100000000000000000000)
  directionLo := (537584149283762945379/100000000000000000000)
  directionHi := (26879207464188147269/5000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree117.table
  base := (109883124220783789771945422465879370065931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-127899021381344108598706622550674512800000000000000)
      constant := (4176790033749444927549095267817544489784861956912272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree117.table
  base := (343384761660375720260934883978317890063/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-15991408545095706935975609984787606600000000000000)
      constant := (522357684191066193413942289258268435325309761242240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537584149283762945379/100000000000000000000)
  centralHi := (26879207464188147269/5000000000000000000)
  directionLo := (539896349843750368879/100000000000000000000)
  directionHi := (6748704373046879611/1250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree118.table
  base := (22545777329822942011181951466458296820257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-386858888744771260207303767409716336000000000000000)
      constant := (12740089157586801999245493089565709305687441255271760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree118.table
  base := (112728886207749932381795271700867813764429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-48369557066082761798071927223201427000000000000000)
      constant := (1593301029674683627713619223839456637012167134913018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539896349843750368879/100000000000000000000)
  centralHi := (6748704373046879611/1250000000000000000)
  directionLo := (271099345069322997537/50000000000000000000)
  directionHi := (21687947605545839803/4000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree119.table
  base := (115606812709093342990007161906211340413251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-390020713345510194618487667167409133600000000000000)
      constant := (12951547258918190114420862090734189712090415615916336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree119.table
  base := (28901703077782057813964681261355737986233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-48764888496878402788217024492040034200000000000000)
      constant := (1619746496819692666384427902727530842868344084643144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271099345069322997537/50000000000000000000)
  centralHi := (21687947605545839803/4000000000000000000)
  directionLo := (2177965180994486399/400000000000000000)
  directionHi := (544491295248621599751/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree120.table
  base := (14814612779998938866937544978615934515869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-131060845982083043009890522308367310400000000000000)
      constant := (4388248134971588011119990311553750067233653077194624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree120.table
  base := (118516901881182947210038884439822415416047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-16386739975891347926120707253626213800000000000000)
      constant := (548803151322458345164826075712447010393676584991658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2177965180994486399/400000000000000000)
  centralHi := (544491295248621599751/100000000000000000000)
  directionLo := (546774287631541598217/100000000000000000000)
  directionHi := (273387143815770799109/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree121.table
  base := (24291831019621482756044725627372467337653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-396344362546988063440855466682794728800000000000000)
      constant := (13379680595283506540435101695930203556057665511217040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree121.table
  base := (121459154774624377006945994762992681825209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-49555551358469684768507219029717248600000000000000)
      constant := (1673289901081208619595347048143992904267347382205778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546774287631541598217/100000000000000000000)
  centralHi := (273387143815770799109/50000000000000000000)
  directionLo := (109809557439858202611/20000000000000000000)
  directionHi := (8578871674988922079/1562500000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree122.table
  base := (7777098197185066793692696010324579952797/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-399506187147726997852039366440487526400000000000000)
      constant := (13596355829762438684777713018578786754354862818364672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree122.table
  base := (248867141726689841954230835894572369221/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-49950882789265325758652316298555855800000000000000)
      constant := (1700387838128540963979963024285375448578097825141000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109809557439858202611/20000000000000000000)
  centralHi := (8578871674988922079/1562500000000000000)
  directionLo := (34456994461954407269/6250000000000000000)
  directionHi := (110262382278254103261/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree123.table
  base := (3186003757392028277080489557010615174407/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-134222670582821977421074422066060108000000000000000)
      constant := (4604923369372443468122504677001424059399049781983360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree123.table
  base := (5097606001312387847569470969805406209941/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-16782071406686988916265804522464821000000000000000)
      constant := (575901088360059689757226629641751133056962106004350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34456994461954407269/6250000000000000000)
  centralHi := (110262382278254103261/20000000000000000000)
  directionLo := (553566775245186005861/100000000000000000000)
  directionHi := (276783387622593002931/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree124.table
  base := (65239446208781390367582511828701760959501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-405829836349204866674407165955873121600000000000000)
      constant := (14034923430138759963204555373488603673505831258912672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree124.table
  base := (65239446090308928360112801444929362910519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-50741545650856607738942510836233070200000000000000)
      constant := (1755236181910022696358248576680485484187510113037596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553566775245186005861/100000000000000000000)
  centralHi := (276783387622593002931/50000000000000000000)
  directionLo := (277906245732626726711/50000000000000000000)
  directionHi := (555812491465253453423/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree125.table
  base := (66774898714389258534264150798367726772303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-408991660949943801085591065713565919200000000000000)
      constant := (14256815795639485179779107747382129626724590879771616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree125.table
  base := (133549797215216498144165198216897561580651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-51136877081652248729087608105071677400000000000000)
      constant := (1782986588594736562455656173972670188798058655220342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277906245732626726711/50000000000000000000)
  centralHi := (555812491465253453423/100000000000000000000)
  directionLo := (55804917048793344467/10000000000000000000)
  directionHi := (558049170487933444671/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree126.table
  base := (546611460988902546548064601364672594901/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-137384495183560911832258321823752905600000000000000)
      constant := (4826815734817364453201550087694088978381600379228000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree126.table
  base := (136652865054750949885046938877026088525883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-17177402837482629906410901791303428200000000000000)
      constant := (603651495037819100041860570391363584785612784925362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/10000000000000000000)
  centralHi := (558049170487933444671/100000000000000000000)
  directionLo := (280138460272651947019/50000000000000000000)
  directionHi := (560276920545303894039/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree127.table
  base := (139788095799495890431118205862990804879397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-415315310151421669907958865228951514400000000000000)
      constant := (14705817656426900360157683012477733185500513203885392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree127.table
  base := (27957619125207396081246174263621293133307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-51927539943243530709377802642748891800000000000000)
      constant := (1839139871447531489807534062464639582348954998399470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280138460272651947019/50000000000000000000)
  centralHi := (560276920545303894039/100000000000000000000)
  directionLo := (140623961931543457703/25000000000000000000)
  directionHi := (562495847726173830813/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree128.table
  base := (142955489019954358965101067403049097489673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20390643360000000000000000000000000000000000000000
      center := (128426836209)
      previous := (0)
      next := (114221819775)
      square := (2986963287711530921273657202656428800000000000000)
      linear := (-418477134752160604319142764986644312000000000000000)
      constant := (14932927151430072357918615557276541469148179342602128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree128.table
  base := (142955488863641978259148923605064503344019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16057552623)
      previous := (0)
      next := (14273529375)
      square := (373370410963941365159207150332053600000000000000)
      linear := (-52322871374039171699522899911587499000000000000000)
      constant := (1867542747580281468449498171125430136818542735225798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell140.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140623961931543457703/25000000000000000000)
  centralHi := (562495847726173830813/100000000000000000000)
  directionLo := (564706056035035897023/100000000000000000000)
  directionHi := (8823532125547435891/1562500000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree129.table
  base := (14615504484991595982209216015190150922537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42808945403)
      previous := (0)
      next := (38073939925)
      square := (995654429237176973757885734218809600000000000000)
      linear := (-140546319784299846243442221581445703200000000000000)
      constant := (5053925229780648898091994115176089197340342317801440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree129.table
  base := (146155044709063546352998415823724550186013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 849610140000000000000000000000000000000000000000
      center := (5352517541)
      previous := (0)
      next := (4757843125)
      square := (124456803654647121719735716777351200000000000000)
      linear := (-17572734268278270896555999060142035400000000000000)
      constant := (632054371165598655705559433292728342940497553097182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell140.Kernel129
