import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell135.Parameters
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch000_049
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch050_099
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch100_149
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch150_199
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree000.table
  base := (679318152181651998999711857/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (183198768192892429140794520000000000000)
      linear := (-12711813605901646322127174250000000000)
      constant := (169829538045412999749927964250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree000.table
  base := (679318152181651998999711857/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (183198768192892429140794520000000000000)
      linear := (-12711813605901646322127174250000000000)
      constant := (169829538045412999749927964250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree001.table
  base := (38086624847297988230532561544345802024267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-51492188077736332885899961282305036500000000000)
      constant := (23829880219531347016269715190795256972499983097815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree001.table
  base := (15222049378823940205460477038712120326831/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-103086811746707721573553997820468073000000000000)
      constant := (47620422533844024680649336179218937888749946233975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49922973248514476683/100000000000000000000)
  directionHi := (12480743312128619171/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree002.table
  base := (113750398881787455822027191579820312090757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-99804910327838051225192014955172156500000000000)
      constant := (14279858485291224670973963943311684602390592043173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree002.table
  base := (45435696612679657029404490259386440869203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-199814691838146214053892180422060313000000000000)
      constant := (28519631690858556322411763612414824951656215086335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922973248514476683/100000000000000000000)
  centralHi := (12480743312128619171/25000000000000000000)
  directionLo := (70601745842038383419/100000000000000000000)
  directionHi := (3530087292101919171/5000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree003.table
  base := (72816129193157842539803484107970668461223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-148117632577939769564484068628039276500000000000)
      constant := (9225990049093244735920890740233475295498964695047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree003.table
  base := (145376064314335358582008972624975572982439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-296542571929584706534230363023652553000000000000)
      constant := (18420437539550981541904506229134732717416027313671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601745842038383419/100000000000000000000)
  centralHi := (3530087292101919171/5000000000000000000)
  directionLo := (21617281532832239199/25000000000000000000)
  directionHi := (86469126131328956797/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree004.table
  base := (49816135817185206160198525245798049770773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-196430354828041487903776122300906396500000000000)
      constant := (6440442744044864959700022484714043302529438514997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree004.table
  base := (99442559220837855004268518738669487633789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-393270452021023199014568545625244793000000000000)
      constant := (12858038862884772536476753860166202040373471473821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21617281532832239199/25000000000000000000)
  centralHi := (86469126131328956797/100000000000000000000)
  directionLo := (49922973248514476683/50000000000000000000)
  directionHi := (99845946497028953367/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree005.table
  base := (14423441737580814058166109584526095806761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-489486154156286412486136351947547033000000000000)
      constant := (9672445403117929634485714079162069346292867025645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree005.table
  base := (35988884116781537191281224498695979675117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-244999166056230845747453364113418516500000000000)
      constant := (4828187798360550477170759034969207170149518035213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922973248514476683/50000000000000000000)
  centralHi := (99845946497028953367/100000000000000000000)
  directionLo := (3488473806955683493/3125000000000000000)
  directionHi := (111631161822581871777/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree006.table
  base := (340598187763669164349799915420268480017/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-146527899664122462291180114823320318250000000000)
      constant := (1938057203448578167872881325018109064899309252520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree006.table
  base := (5439101629470725061703693027634344295847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-293363106101950091987622455414214636500000000000)
      constant := (3870551154082991172387777756586332635193453210915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/3125000000000000000)
  centralHi := (111631161822581871777/100000000000000000000)
  directionLo := (122285810901475206619/100000000000000000000)
  directionHi := (6114290545073760331/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree007.table
  base := (42442080507545014632187696268791723639011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-682737043156693285843304566639015513000000000000)
      constant := (6579266490128442277933647150560859429223936125379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree007.table
  base := (8472188730258149979042437308447260448909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-683454092295338676455583093430021513000000000000)
      constant := (6571791954726617475783023576311556055702350737505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122285810901475206619/100000000000000000000)
  centralHi := (6114290545073760331/5000000000000000000)
  directionLo := (4127617872640614369/3125000000000000000)
  directionHi := (132083771924499659809/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree008.table
  base := (8428834379470921667812261518828711735651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-194840621914224180630472168496187438250000000000)
      constant := (1468325574386666373928783829304887329188817142339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree008.table
  base := (33650493562714954944602562006169409033621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-780181972386777168935921276031613753000000000000)
      constant := (5868679363559737717160292386565219735176626079669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4127617872640614369/3125000000000000000)
  centralHi := (132083771924499659809/100000000000000000000)
  directionLo := (70601745842038383419/50000000000000000000)
  directionHi := (141203491684076766839/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree009.table
  base := (13553792274805358858683268468918902629347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-437993966078550079600236390665241996500000000000)
      constant := (2741638657021822375839707423939857597516892223683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree009.table
  base := (2705449850005074732928037185575862153361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-438454926239107830708129729316602996500000000000)
      constant := (2740523449669037400044883220171917332293831462645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601745842038383419/50000000000000000000)
  centralHi := (141203491684076766839/100000000000000000000)
  directionLo := (149768919745543430049/100000000000000000000)
  directionHi := (2995378394910868601/2000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree010.table
  base := (685425748867767780566194854976231864699/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-243153344164325898969764222169054558250000000000)
      constant := (1330875268256835937937130416749849864408192630488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree010.table
  base := (5472364648300719449189738737986450004261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-243409433142413538474149410308699558250000000000)
      constant := (1330854104393987617931957979070157987081928482629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149768919745543430049/100000000000000000000)
  centralHi := (2995378394910868601/2000000000000000000)
  directionLo := (157870303032960954689/100000000000000000000)
  directionHi := (15787030303296095469/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree011.table
  base := (2222608742111513830415392759345615053711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-267309705289376758139410249005488118250000000000)
      constant := (1335593950561642288135638252254748722390610427358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree011.table
  base := (709751439828313337899152260410344751439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1070365612661092646376935823836390473000000000000)
      constant := (5344314952516027351710668820936447399969833866775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157870303032960954689/100000000000000000000)
  centralHi := (15787030303296095469/10000000000000000000)
  directionLo := (165575770684272561201/100000000000000000000)
  directionHi := (82787885342136280601/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree012.table
  base := (14384993717135452264458846861285665107427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1165864265657710469236225103367686713000000000000)
      constant := (5506844683067466087819315446385657487359950724803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree012.table
  base := (7176862214662287247499040217920856815209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-583546746376265569428637003218991356500000000000)
      constant := (2755378639390469592758595376736011821252204968201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165575770684272561201/100000000000000000000)
  centralHi := (82787885342136280601/50000000000000000000)
  directionLo := (172938252262657913593/100000000000000000000)
  directionHi := (86469126131328956797/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree013.table
  base := (11566691105565431783974879845075470797591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1262489710157913905914809210713420953000000000000)
      constant := (5794484023995898965507358624981296290881152890999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree013.table
  base := (1442537485623723596500646031308933382693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-315955343210992407834403047259893738250000000000)
      constant := (1450090249563236696213981363458161861261756047754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172938252262657913593/100000000000000000000)
  centralHi := (86469126131328956797/50000000000000000000)
  directionLo := (179999839871135988329/100000000000000000000)
  directionHi := (17999983987113598833/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree014.table
  base := (4599234500568834442480514256788430647227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-679557577329058671296696659029577596500000000000)
      constant := (3094674801482116108426116654552033621354147887003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree014.table
  base := (229405435546981564273268150175106999007/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-340137313233852030954487592910291798250000000000)
      constant := (1549301667670072186157863833980824323036389274230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179999839871135988329/100000000000000000000)
  centralHi := (17999983987113598833/10000000000000000000)
  directionLo := (93397330812511030149/50000000000000000000)
  directionHi := (186794661625022060299/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree015.table
  base := (718641271101971646398112821115790292113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-727870299579160389635988712702444716500000000000)
      constant := (3339848248238624022239341301400389872564062551285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree015.table
  base := (716769052620973900669587955783756468917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-728638566513423308149144277121379716500000000000)
      constant := (3344782701287069751020042337074741499391022017065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93397330812511030149/50000000000000000000)
  centralHi := (186794661625022060299/100000000000000000000)
  directionLo := (48337710996163738761/25000000000000000000)
  directionHi := (38670168796930991009/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree016.table
  base := (5459611727140585650134882491547523840041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1552366043658524215950561532750623673000000000000)
      constant := (7256656672630858204467228462552257598650845199049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree016.table
  base := (136097501226479201256918088985563924421/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-388501253279571277194656684211087918250000000000)
      constant := (1817145146839723144904912174365656664649248808690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48337710996163738761/25000000000000000000)
  centralHi := (38670168796930991009/20000000000000000000)
  directionLo := (199691892994057906733/100000000000000000000)
  directionHi := (99845946497028953367/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree017.table
  base := (198181929772482092100785051353517493099/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-412247872039681913157286410024089478250000000000)
      constant := (1978355865458479838360061005186768987322609832055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree017.table
  base := (1975245002114884034933937613124730311693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-825366446604861800629482459722971956500000000000)
      constant := (3963727246588281176781490043628738277168137304877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199691892994057906733/100000000000000000000)
  centralHi := (99845946497028953367/50000000000000000000)
  directionLo := (51459422962127503203/25000000000000000000)
  directionHi := (205837691848510012813/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree018.table
  base := (664068649744266358050199795827258219193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-436404233164732772326932436860523038250000000000)
      constant := (2161179253228987555717813806011987357413326572377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree018.table
  base := (2645301517685257295934630832574874592397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1747460773301162093739303102047536153000000000000)
      constant := (8660914752783356058312053027826166807264252105133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51459422962127503203/25000000000000000000)
  centralHi := (205837691848510012813/100000000000000000000)
  directionLo := (211805237526115150257/100000000000000000000)
  directionHi := (105902618763057575129/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree019.table
  base := (1504553518798871464819662319099816223493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1842242377159134525986313854787826393000000000000)
      constant := (9446414587384055124335407961263920266403944375077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree019.table
  base := (149542045695225221910014769170138761743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-922094326696300293109820642324564196500000000000)
      constant := (4732422570795637023041586432168466033388361646635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211805237526115150257/100000000000000000000)
  centralHi := (105902618763057575129/50000000000000000000)
  directionLo := (217609195351359060019/100000000000000000000)
  directionHi := (10880459767567953001/5000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree020.table
  base := (482628023475512053635955578299623089971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-1938867821659337962664897962133560633000000000000)
      constant := (10315283731176390564788956062052846762524374284819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree020.table
  base := (237522789752214539045265269255020018283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-970458266742019539349989733625360316500000000000)
      constant := (5168009484697204599121434132947237856671242637387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609195351359060019/100000000000000000000)
  centralHi := (10880459767567953001/5000000000000000000)
  directionLo := (3488473806955683493/1562500000000000000)
  directionHi := (223262323645163743553/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree021.table
  base := (-429818768019317132036877012216003996433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2035493266159541399343482069479294873000000000000)
      constant := (11248783625533733129077751817245886533084131197263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree021.table
  base := (-109024770729522421738310482967342925283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-509411103393869392795079412463078218250000000000)
      constant := (2817975133490800251988150779017904219888842839613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/1562500000000000000)
  centralHi := (223262323645163743553/100000000000000000000)
  directionLo := (114387901914286518767/50000000000000000000)
  directionHi := (45755160765714607507/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree022.table
  base := (-1248781225900759485071284792759589672827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2132118710659744836022066176825029113000000000000)
      constant := (12244914022690100164427440470165168146666578194597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree022.table
  base := (-626985855845405356707925288145694917557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1067186146833458031830327916226952556500000000000)
      constant := (6135247056644729649012470465241022182810424451627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114387901914286518767/50000000000000000000)
  centralHi := (45755160765714607507/20000000000000000000)
  directionLo := (234159500502075776399/100000000000000000000)
  directionHi := (585398751255189441/250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree023.table
  base := (-496715663926805245852055340334770414339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-557186038789987068175162571042690838250000000000)
      constant := (3325524689923786937340545272917776560925446387229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree023.table
  base := (-995571904451101060066305693017900725801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1115550086879177278070497007527748676500000000000)
      constant := (6665113760873018906362772908051389771253597824311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234159500502075776399/100000000000000000000)
  centralHi := (585398751255189441/250000000000000000)
  directionLo := (59855542210680832377/25000000000000000000)
  directionHi := (239422168842723329509/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree024.table
  base := (-165874994924436304682126463599752538061/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-581342399915037927344808597879124398250000000000)
      constant := (3604773784436473998039626318451145191254553156684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree024.table
  base := (-531504898448637236767116853779599556937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2327828053849793048621332197657089593000000000000)
      constant := (14449861530138068952187589770947543665924161874035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59855542210680832377/25000000000000000000)
  centralHi := (239422168842723329509/100000000000000000000)
  directionLo := (122285810901475206619/50000000000000000000)
  directionHi := (244571621802950413239/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree025.table
  base := (-1629015136751599381905798536719561277241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1210997522080177573028909249431115916500000000000)
      constant := (7797461516658893945077427068057659186614053210151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree025.table
  base := (-1630463497289330247188522701247368455777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1212277966970615770550835190129340916500000000000)
      constant := (7814209509778015308893407775378355866450809282047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122285810901475206619/50000000000000000000)
  centralHi := (244571621802950413239/100000000000000000000)
  directionLo := (31201858280321547927/12500000000000000000)
  directionHi := (249614866242572383417/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree026.table
  base := (-3805136305621203487825691615670717274827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2518620488660558582736402606207966073000000000000)
      constant := (16828809255392812031120406610142697758346662816597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree026.table
  base := (-1903756618898056591514629881220932530237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1260641907016335016791004281430137036500000000000)
      constant := (8432564691598707814166374388903584276915083731107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31201858280321547927/12500000000000000000)
  centralHi := (249614866242572383417/100000000000000000000)
  directionLo := (127279107385372948041/50000000000000000000)
  directionHi := (254558214770745896083/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree027.table
  base := (-2150097948687056815665576525624316595267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1307622966580381009707493356776850156500000000000)
      constant := (9060071889255996331986420534901442477371689161437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree027.table
  base := (-4302143441305364999774234797821748524177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2618011694124108526062346745461866313000000000000)
      constant := (18159384804506403919251042841322479881229920234447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127279107385372948041/50000000000000000000)
  centralHi := (254558214770745896083/100000000000000000000)
  directionLo := (25940737839398687039/10000000000000000000)
  directionHi := (259407378393986870391/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree028.table
  base := (-14834555792176451494232290961631260081/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-677967844415241364023392705224858638250000000000)
      constant := (4867111318280492006366091000828579544127523311280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree028.table
  base := (-37098839029161695735586713799897468147/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-678684893553886754635671232015864638250000000000)
      constant := (4877676457896584946252970255722741449946556899744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25940737839398687039/10000000000000000000)
  centralHi := (259407378393986870391/100000000000000000000)
  directionLo := (264167543848999319617/100000000000000000000)
  directionHi := (132083771924499659809/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree029.table
  base := (-5148759145054002529730842494676434003749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2808496822161168892772154928245168793000000000000)
      constant := (20873333937173148072721900168933294057648925975739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree029.table
  base := (-515006137237003507372244582700029080929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1405733727153492755511511555332525396500000000000)
      constant := (10459357125307428812150916510232954730894398073595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264167543848999319617/100000000000000000000)
  centralHi := (132083771924499659809/50000000000000000000)
  directionLo := (134421719302708733009/50000000000000000000)
  directionHi := (268843438605417466019/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree030.table
  base := (-2753848108988636038373315315560848043357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1452561133330686164725369517795451516500000000000)
      constant := (11167255036181021403630198636419301902791123735427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree030.table
  base := (-5508759121987726947543423019914211662521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-2908195334398424003503361293266643033000000000000)
      constant := (22383111700819736373761932513398425793147283288231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134421719302708733009/50000000000000000000)
  centralHi := (268843438605417466019/100000000000000000000)
  directionLo := (136719692929691699943/50000000000000000000)
  directionHi := (273439385859383399887/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree031.table
  base := (-291288005885092151728975639514925493589/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-750436927790393941532330785734159318250000000000)
      constant := (5962934296378201018259733123755591888368434419895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree031.table
  base := (-5826626718165705936847895189732342781813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3004923214489862495983699475868235273000000000000)
      constant := (23903662811040809179088669167719004526683627726443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136719692929691699943/50000000000000000000)
  centralHi := (273439385859383399887/100000000000000000000)
  directionLo := (277959351339595434931/100000000000000000000)
  directionHi := (69489837834898858733/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree032.table
  base := (-6104443091151069855153125734704854255001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3098373155661779202807907250282371513000000000000)
      constant := (25424828656987735340134060754944973697050099245511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree032.table
  base := (-1526287226952426271461879949152527104399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-775412773645325247116009414617456878250000000000)
      constant := (6370045474897187683650629673404392611265211407889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277959351339595434931/100000000000000000000)
  centralHi := (69489837834898858733/25000000000000000000)
  directionLo := (282406983368153533677/100000000000000000000)
  directionHi := (141203491684076766839/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree033.table
  base := (-6344922695562216758999483325401468432121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3194998600161982639486491357628105753000000000000)
      constant := (27053637222080476093368065091001249194529316553831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree033.table
  base := (-3172748499048706866911276639406870748859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1599189487336369740472187920535709876500000000000)
      constant := (13556261241693228589666172296567794206183646126949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282406983368153533677/100000000000000000000)
  centralHi := (141203491684076766839/50000000000000000000)
  directionLo := (286785647327533528137/100000000000000000000)
  directionHi := (143392823663766764069/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree034.table
  base := (-13096256328915822202483680982418502627/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-822906011165546519041268866243459998250000000000)
      constant := (7184511667830381221442952427444030263915277799625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree034.table
  base := (-6548595028772294704853931771121875780363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3295106854764177973424714023673011993000000000000)
      constant := (28800569002495795361408088098616007362686326985493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286785647327533528137/100000000000000000000)
  centralHi := (143392823663766764069/50000000000000000000)
  directionLo := (291098455459736733297/100000000000000000000)
  directionHi := (145549227729868366649/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree035.table
  base := (-1678698193913285364379415594592880807347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-847062372290597378210914893079893558250000000000)
      constant := (7619491325340511052383808842706272342570276734317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree035.table
  base := (-671517197260465179877604300826263779047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1695917367427808232952526103137302116500000000000)
      constant := (15272115145977308086623851197662930119440866365085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291098455459736733297/100000000000000000000)
  centralHi := (145549227729868366649/50000000000000000000)
  directionLo := (73837073186939864829/25000000000000000000)
  directionHi := (295348292747759459317/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree036.table
  base := (-6845495174721376574575845137224954901887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3484874933662592949522243679665308473000000000000)
      constant := (32273320747082303951232454710272982919921966644257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree036.table
  base := (-6845802915014665922907418790193095356939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3488562614947054958385390388876196473000000000000)
      constant := (32343434431874140440294375536132265916332936055829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837073186939864829/25000000000000000000)
  centralHi := (295348292747759459317/100000000000000000000)
  directionLo := (299537839491086860099/100000000000000000000)
  directionHi := (2995378394910868601/1000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree037.table
  base := (-1388138396739787626957667067805191766867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3581500378162796386200827787011042713000000000000)
      constant := (34124055903563775581826411781983172668943029245185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree037.table
  base := (-867617692510139157266411352290444829231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-896322623759623362716432142869447178250000000000)
      constant := (8549531171188827244405369748947062606959857754082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299537839491086860099/100000000000000000000)
  centralHi := (2995378394910868601/1000000000000000000)
  directionLo := (303669591077144250487/100000000000000000000)
  directionHi := (37958698884643031311/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree038.table
  base := (-7000743533113591036189338143859571172113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3678125822662999822879411894356776953000000000000)
      constant := (36030125708054785722856811784114260800456417169743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree038.table
  base := (-7000945758495397608874024102835844348861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3682018375129931943346066754079380953000000000000)
      constant := (36108256290469947188754795627992995976347905607971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303669591077144250487/100000000000000000000)
  centralHi := (37958698884643031311/12500000000000000000)
  directionLo := (30774587536298825117/10000000000000000000)
  directionHi := (307745875362988251171/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree039.table
  base := (-7025934167626130174320578314314534870407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3774751267163203259557996001702511193000000000000)
      constant := (37991494600557355486353398239678252803334219357977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree039.table
  base := (-878262240668870103982546806282946398977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-944686563805342608956601234170243298250000000000)
      constant := (9518448484458588171960279064482906336796592514494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30774587536298825117/10000000000000000000)
  centralHi := (307745875362988251171/100000000000000000000)
  directionLo := (311768868011069686333/100000000000000000000)
  directionHi := (155884434005534843167/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree040.table
  base := (-701648826965355686828723588072859753619/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1935688355831703348118290054524122716500000000000)
      constant := (20004067259960537051218275698414052732218709796545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree040.table
  base := (-3508310394961347886148564478482573604953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1937737067656404464153371559641282716500000000000)
      constant := (20047354884969016127564561996000881134559689950983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311768868011069686333/100000000000000000000)
  centralHi := (155884434005534843167/50000000000000000000)
  directionLo := (157870303032960954689/50000000000000000000)
  directionHi := (315740606065921909379/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree041.table
  base := (-6972582903980940983206106569579864237051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-3968002156163610132915164216393979673000000000000)
      constant := (42080023322514400838945465856693083194325027073061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree041.table
  base := (-3486345039221158392741435623148506308851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-1986101007702123710393540650942078836500000000000)
      constant := (21085490905274121898875606759921340932026817762861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157870303032960954689/50000000000000000000)
  centralHi := (315740606065921909379/100000000000000000000)
  directionLo := (79915750003068690823/25000000000000000000)
  directionHi := (319663000012274763293/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree042.table
  base := (-861794724490923075235581841111306960047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1016156900165953392398437080934928478250000000000)
      constant := (11051785883590082106866351110630955354158757528034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree042.table
  base := (-3447222210327584402570509990742056418061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2034464947747842956633709742242874956500000000000)
      constant := (22151296361349937139083597618049204682798120969171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79915750003068690823/25000000000000000000)
  centralHi := (319663000012274763293/100000000000000000000)
  directionLo := (323537844517174632483/100000000000000000000)
  directionHi := (80884461129293658121/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree043.table
  base := (-3390961602679986893423867165085492899093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2080626522582008503136166215542724076500000000000)
      constant := (23194740683208110938548993433421791097476300856523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree043.table
  base := (-6781993180889186822953427794692753965067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4165657775587124405747757667087342153000000000000)
      constant := (46489528829345957317892117400016921569875997129237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323537844517174632483/100000000000000000000)
  centralHi := (80884461129293658121/25000000000000000000)
  directionLo := (163683414013753512831/50000000000000000000)
  directionHi := (327366828027507025663/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree044.table
  base := (-6635366140271656155964817752362153863247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4257878489664220442950916538431182393000000000000)
      constant := (48627025937506944243148689645242427316922954299217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree044.table
  base := (-3317711317996602325331448069655109889073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2131192827839281449114047924844467196500000000000)
      constant := (24365889670373932615091751531204573724533683936303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163683414013753512831/50000000000000000000)
  centralHi := (327366828027507025663/100000000000000000000)
  directionLo := (331151541368545122403/100000000000000000000)
  directionHi := (82787885342136280601/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree045.table
  base := (-1290951052013705449811212233292980618703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4354503934164423879629500645776916633000000000000)
      constant := (50919768661122254173922424895074782205190494886165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree045.table
  base := (-6454800849119066034345744418972433205163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4359113535770001390708434032290526633000000000000)
      constant := (51029335744962608706749201963655593739525683058293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331151541368545122403/100000000000000000000)
  centralHi := (82787885342136280601/25000000000000000000)
  directionLo := (10465421420867050479/3125000000000000000)
  directionHi := (334893485467745615329/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree046.table
  base := (-3120072372437156993025668066310052988517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2225564689332313658154042376561325436500000000000)
      constant := (26633851380761782212018609481596898289193141112187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree046.table
  base := (-780022689331657411133259267583878728159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1113960353965359970797193053723029718250000000000)
      constant := (13345547831749412837600706641761939142111931098498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10465421420867050479/3125000000000000000)
  centralHi := (334893485467745615329/100000000000000000000)
  directionLo := (338594078310160403373/100000000000000000000)
  directionHi := (169297039155080201687/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree047.table
  base := (-5991577348893162024419557083799338266367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4547754823164830752986668860468385113000000000000)
      constant := (55670822891891951935888440377227320421369997093537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree047.table
  base := (-1497901747871724400142963320895902131051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1138142323988219593917277599373427778250000000000)
      constant := (13947585197367928984873393478580330694734250907061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338594078310160403373/100000000000000000000)
  centralHi := (169297039155080201687/50000000000000000000)
  directionLo := (8556366530421913259/2500000000000000000)
  directionHi := (342254661216876530361/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree048.table
  base := (-713635851236543565461795679365103433513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1161095066916258547416313241953529838250000000000)
      constant := (14532281208249870256745860115879110806345437490286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree048.table
  base := (-2854555347982280909602131754277597182399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2324648588022158434074724290047651676500000000000)
      constant := (29126889976676912472479295175657421114221341265889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8556366530421913259/2500000000000000000)
  centralHi := (342254661216876530361/100000000000000000000)
  directionLo := (345876504525315827187/100000000000000000000)
  directionHi := (86469126131328956797/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree049.table
  base := (-5392699750583062499800486100250773690227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4741005712165237626343837075159853593000000000000)
      constant := (60642605255423494604408260261817465194945567085997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree049.table
  base := (-2696359494841402843859279295831239359443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2373012528067877680314893381348447796500000000000)
      constant := (30386252760938092065783933194363421734596371095373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345876504525315827187/100000000000000000000)
  centralHi := (86469126131328956797/25000000000000000000)
  directionLo := (174730406369800668391/50000000000000000000)
  directionHi := (349460812739601336783/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree050.table
  base := (-1008487435809043962504247309448179099737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4837631156665441063022421182505587833000000000000)
      constant := (63211261531904253519575402438926100274032053728035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree050.table
  base := (-5042452668774804826731557961144125252043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4842752936227193853110124945298487833000000000000)
      constant := (63346514894285005380259804724056527053127506213973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174730406369800668391/50000000000000000000)
  centralHi := (349460812739601336783/100000000000000000000)
  directionLo := (44126091151273989637/12500000000000000000)
  directionHi := (353008729210191917097/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree051.table
  base := (-2329157836373958266304429720481940369361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2467128300582822249850502644925661036500000000000)
      constant := (32917545794635971852292341840772179986429242083471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree051.table
  base := (-931665627761373301023585970545830987791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-4939480816318632345590463127900080073000000000000)
      constant := (65975806018908549548371953742699090074682461506005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44126091151273989637/12500000000000000000)
  centralHi := (353008729210191917097/100000000000000000000)
  directionLo := (356521340394325478483/100000000000000000000)
  directionHi := (89130335098581369621/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree052.table
  base := (-4240348312887340765259601923904591591163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5030882045665847936379589397197056313000000000000)
      constant := (68514093791598854366252383077315377236855458304293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree052.table
  base := (-4240358341653735559650061649225420052787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5036208696410070838070801310501672313000000000000)
      constant := (68660377277242574344612170269250535143388104754157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356521340394325478483/100000000000000000000)
  centralHi := (89130335098581369621/25000000000000000000)
  directionLo := (179999839871135988329/50000000000000000000)
  directionHi := (359999679742271976659/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree053.table
  base := (-3788545421694026097881576424861050895811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6054856)
      previous := (3027428)
      next := (3027428)
      square := (32624769434863055351109251299680000000000000)
      linear := (-1825385364957654458190877004109217000000000000)
      constant := (25364281540759027993570631986984379653067598469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree053.table
  base := (-1894276743354847133189567229606677230707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16312384717431527675554625649840000000000000)
      linear := (-913659055981044736659156193147608500000000000)
      constant := (12709189639107413283733666190178949748011693653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179999839871135988329/50000000000000000000)
  centralHi := (359999679742271976659/100000000000000000000)
  directionLo := (72688946249759400481/20000000000000000000)
  directionHi := (181722365624398501203/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree054.table
  base := (-3302915144258382496498319001670349916011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5224132934666254809736757611888524793000000000000)
      constant := (74037609739830864978495839422549414520052471421621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree054.table
  base := (-330292162773998555043461114885138221979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2614832228296473911515738837852428396500000000000)
      constant := (37097677678748702096202548509668627896074688456345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72688946249759400481/20000000000000000000)
  centralHi := (181722365624398501203/50000000000000000000)
  directionLo := (366857432704425619857/100000000000000000000)
  directionHi := (183428716352212809929/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree055.table
  base := (-2783463907661820148715998841174703459103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5320758379166458246415341719234259033000000000000)
      constant := (76882121663347603480458763938892220553178046421633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree055.table
  base := (-1391734558978886810713256437421438434563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2663196168342193157755907929153224516500000000000)
      constant := (38522880188844425806826666611424885323603591281693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366857432704425619857/100000000000000000000)
  centralHi := (183428716352212809929/50000000000000000000)
  directionLo := (74047735735390063161/20000000000000000000)
  directionHi := (185119339338475157903/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree056.table
  base := (-2230196783286762625381984548105730066521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5417383823666661683093925826579993273000000000000)
      constant := (79781801984317830724476951585765161347908947732231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree056.table
  base := (-223020096903317022829523274285031779131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2711560108387912403996077020454020636500000000000)
      constant := (39975720913161443439932531706854805785765581379705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74047735735390063161/20000000000000000000)
  centralHi := (185119339338475157903/50000000000000000000)
  directionLo := (93397330812511030149/25000000000000000000)
  directionHi := (373589323250044120597/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree057.table
  base := (-1643117772722816275303674509099346199303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5514009268166865119772509933925727513000000000000)
      constant := (82736650202304795352857393361516124762581074663833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree057.table
  base := (-821560567157122705022997195677088812037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2759924048433631650236246111754816756500000000000)
      constant := (41456199604497910256413042127678844960284035730907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93397330812511030149/25000000000000000000)
  centralHi := (373589323250044120597/100000000000000000000)
  directionLo := (376910182542735038551/100000000000000000000)
  directionHi := (47113772817841879819/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree058.table
  base := (-1022230033380870542446365302993460001099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5610634712667068556451094041271461753000000000000)
      constant := (85746665922444304968702295142262193790920619621589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree058.table
  base := (-40889309290355149851006839916994655357/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5616575976958701792952830406111225753000000000000)
      constant := (85928632135714903624288538491953743956133061685675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376910182542735038551/100000000000000000000)
  centralHi := (47113772817841879819/12500000000000000000)
  directionLo := (380202037030799902961/100000000000000000000)
  directionHi := (190101018515399951481/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree059.table
  base := (-45942007066166282881615072202607228733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1426815039291817998282419537154298998250000000000)
      constant := (22202962208294901475336498930077181053388889805126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree059.table
  base := (-73507644539793676103228302331636603933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5713303857050140285433168588712817993000000000000)
      constant := (89000140298854816006522093097680496049642218148815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380202037030799902961/100000000000000000000)
  centralHi := (190101018515399951481/50000000000000000000)
  directionLo := (191732816844392624683/50000000000000000000)
  directionHi := (383465633688785249367/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree060.table
  base := (40120274026803835112029853297620681799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1450971400416868857452065563990732558250000000000)
      constant := (22983049672172898450896519339330160122263229081422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree060.table
  base := (32096045410587367312587374015542390021/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2905015868570789388956753385657205116500000000000)
      constant := (46063461727883841026852244213087294974269324796345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191732816844392624683/50000000000000000000)
  centralHi := (383465633688785249367/100000000000000000000)
  directionLo := (48337710996163738761/12500000000000000000)
  directionHi := (386701687969309910089/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree061.table
  base := (104326316202003809910953075197925965777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-2950255523083839433243423181654332236500000000000)
      constant := (47553857647517107276752943013868954560949515539765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree061.table
  base := (1043261767769952415858281981229459826621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5906759617233017270393844953916002473000000000000)
      constant := (95308981415064248776376867207848545326913250856669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48337710996163738761/12500000000000000000)
  centralHi := (386701687969309910089/100000000000000000000)
  directionLo := (97477721408626692203/25000000000000000000)
  directionHi := (389910885634506768813/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree062.table
  base := (1799365629359730753396205302544652562607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-5997136490667882303165430470654398713000000000000)
      constant := (98338398499193711553343279264961258000162171927823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree062.table
  base := (1799364511241484160540940697944659335817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6003487497324455762874183136517594713000000000000)
      constant := (98546314025791236910086947348561961310316353417513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97477721408626692203/25000000000000000000)
  centralHi := (389910885634506768813/100000000000000000000)
  directionLo := (196546942226441994713/50000000000000000000)
  directionHi := (393093884452883989427/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree063.table
  base := (2589268628973346520441701927962946034699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6093761935168085739844014578000132953000000000000)
      constant := (101624248180455142175899383140333846613534033208811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree063.table
  base := (2589267732532167536538077756676549622043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6100215377415894255354521319119186953000000000000)
      constant := (101838921168893475951445019580163321611765840716027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196546942226441994713/50000000000000000000)
  centralHi := (393093884452883989427/100000000000000000000)
  directionLo := (198125657886749489713/50000000000000000000)
  directionHi := (396251315773498979427/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree064.table
  base := (426621424924010869902263691470413680027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1547596844917072294130649671336466798250000000000)
      constant := (26241316060897401899673812614348400794885572252406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree064.table
  base := (3412970680859566490239427333527739259297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6196943257507332747834859501720779193000000000000)
      constant := (105186802750478498097411407453561854471092921319233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198125657886749489713/50000000000000000000)
  centralHi := (396251315773498979427/100000000000000000000)
  directionLo := (199691892994057906733/50000000000000000000)
  directionHi := (399383785988115813467/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree065.table
  base := (266904583746931303907064865415118916443/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1571753206042123153300295698172900358250000000000)
      constant := (27090361653369560864399516643710734011383381110508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree065.table
  base := (1067618191039926015193946064190147471867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1573417784399692810078799421080592858250000000000)
      constant := (27147489674125771233488008793535973398228828895963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199691892994057906733/50000000000000000000)
  centralHi := (399383785988115813467/100000000000000000000)
  directionLo := (201245938945468527719/50000000000000000000)
  directionHi := (402491877890937055439/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree066.table
  base := (1032354795373350595530081118831794918389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6383638268668696049879766900037335673000000000000)
      constant := (111812795230869985467039174885477703220232625216105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree066.table
  base := (645221689446195028730258405745874129899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1597599754422552433198883966730990918250000000000)
      constant := (28012097237145396436145224657719533805211977123222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201245938945468527719/50000000000000000000)
  centralHi := (402491877890937055439/100000000000000000000)
  directionLo := (405576151944545276587/100000000000000000000)
  directionHi := (101394037986136319147/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree067.table
  base := (6086872936470943529220635807537711112133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6480263713168899486558351007383069913000000000000)
      constant := (115319310049034016977811438928126626353412974680037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree067.table
  base := (6086872566985873926112349640616164548541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6487126897781648225275874049525555913000000000000)
      constant := (115562093460679194800484384883147123018330453155549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405576151944545276587/100000000000000000000)
  centralHi := (101394037986136319147/25000000000000000000)
  directionLo := (408637147459842139863/100000000000000000000)
  directionHi := (51079643432480267483/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree068.table
  base := (7045769924086807386258494560123010121179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-6576889157669102923236935114728804153000000000000)
      constant := (118880991031118224828412228471156754896896473817531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree068.table
  base := (3522884814103195325886946981408566931933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3291927388936543358878106116063574076500000000000)
      constant := (59565536098251683223759040682137331705229838762237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408637147459842139863/100000000000000000000)
  centralHi := (51079643432480267483/12500000000000000000)
  directionLo := (51459422962127503203/12500000000000000000)
  directionHi := (658680613915232041/160000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree069.table
  base := (803846470736226755109093151625407098037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3336757301084653179957759611037269196500000000000)
      constant := (61248919074032388500711948825259535322737400615465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree069.table
  base := (1004808058809381677103804728806301071171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1670145664491131302559137603682185098250000000000)
      constant := (30688831281861496273214544347210742484694095783238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51459422962127503203/12500000000000000000)
  centralHi := (658680613915232041/160000000000000000)
  directionLo := (132701235486057931/32000000000000000)
  directionHi := (51836420111741379297/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree070.table
  base := (453247855155888707136406194800314011717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1692535011667377449148525832355068158250000000000)
      constant := (31542462844241333148369962103788910495474340163065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree070.table
  base := (453247845675070965056870915362299834663/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1694327634513990925679222149332583158250000000000)
      constant := (31608713057740005018331931527478444460313696336035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132701235486057931/32000000000000000)
  centralHi := (51836420111741379297/12500000000000000000)
  directionLo := (407896055886348299/97656250000000000)
  directionHi := (417685561227620658177/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree071.table
  base := (632827935435517167137260460699131283271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1716691372792428308318171859191501718250000000000)
      constant := (32474257674940792680330236283361924207994142034076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree071.table
  base := (1265655851902606273289781116036762783273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1718509604536850548799306694982981218250000000000)
      constant := (32542413372319735085218157528655287900718178254994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407896055886348299/97656250000000000)
  centralHi := (417685561227620658177/100000000000000000000)
  directionLo := (420658449714259677491/100000000000000000000)
  directionHi := (105164612428564919373/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree072.table
  base := (5609667092567099154411928502848065289343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3481695467834958334975635772055870556500000000000)
      constant := (66839688051114538198736892227536308267723872725727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree072.table
  base := (2804833515929215145753128624608340986551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1742691574559710171919391240633379278250000000000)
      constant := (33489932222101631852379390235457594025415823932439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420658449714259677491/100000000000000000000)
  centralHi := (105164612428564919373/25000000000000000000)
  directionLo := (84722095010446060103/20000000000000000000)
  directionHi := (105902618763057575129/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree073.table
  base := (12347218667979805821686030055498076757511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7060016380170120106629855651457475353000000000000)
      constant := (137516887573153249878331969464019134296277102571879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree073.table
  base := (246944371416983084813138853068271487347/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3533747089165139590078951572567554676500000000000)
      constant := (68902539208660000434929229893750249268147144642075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84722095010446060103/20000000000000000000)
  centralHi := (105902618763057575129/25000000000000000000)
  directionLo := (426542070412694604467/100000000000000000000)
  directionHi := (106635517603173651117/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree074.table
  base := (3377225086228652575246580765908409356759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1789160456167580885827109939700802398250000000000)
      constant := (35352391275926920235611264718575442854209099236151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree074.table
  base := (6754450133613622136416409766782723090503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3582111029210858836319120663868350796500000000000)
      constant := (70852851033670710945209300628152030060976805932967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426542070412694604467/100000000000000000000)
  centralHi := (106635517603173651117/25000000000000000000)
  directionLo := (107363413545397302043/25000000000000000000)
  directionHi := (429453654181589208173/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree075.table
  base := (14704379160370397286488513091539468311607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7253267269170526979987023866148943833000000000000)
      constant := (145357408686943037084773499825933717667881264188823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree075.table
  base := (2940875819649114441537176102137990079089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7260949938513156165118579510338293833000000000000)
      constant := (145661599831641847232148270131367715302639699627605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107363413545397302043/25000000000000000000)
  centralHi := (429453654181589208173/100000000000000000000)
  directionLo := (27021601916040298999/6250000000000000000)
  directionHi := (86469126131328956797/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree076.table
  base := (7966827535313498133195405700826824232703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3674946356835365208332803986747339036500000000000)
      constant := (74680209158695848061059246075054762055034654268767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree076.table
  base := (1991706877619501743030550696553198375851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1839419454651148664399729423234971518250000000000)
      constant := (37418192926212551610367839676123615301149112000278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27021601916040298999/6250000000000000000)
  centralHi := (86469126131328956797/20000000000000000000)
  directionLo := (217609195351359060019/50000000000000000000)
  directionHi := (435218390702718120039/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree077.table
  base := (8598364020653897263235638264822073656081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3723259079085466926672096040420206156500000000000)
      constant := (76709296995377268217444268407355957636599851602609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree077.table
  base := (8598364000800486406282002667386438831923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3727202849348016575039627937770739156500000000000)
      constant := (76869608841372395864488259990452149144475047267347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609195351359060019/50000000000000000000)
  centralHi := (435218390702718120039/100000000000000000000)
  directionLo := (438072312368444132681/100000000000000000000)
  directionHi := (219036156184222066341/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree078.table
  base := (2311699755675466892766974432114925498221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1885785900667784322505694047046536638250000000000)
      constant := (39382983925913454791430495628306895763911177338138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree078.table
  base := (9246799006833792199725983204879898520971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-3775566789393735821279797029071535276500000000000)
      constant := (78930468881004958909611794182886993161154489043819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438072312368444132681/100000000000000000000)
  centralHi := (219036156184222066341/50000000000000000000)
  directionLo := (88181552293392427513/20000000000000000000)
  directionHi := (220453880733481068783/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree079.table
  base := (19824265061714330807633665583208714866027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7639769047171340726701360295531880793000000000000)
      constant := (161700443453438222205610659617075702000992040080203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree079.table
  base := (4956066259088250732476919746227132702213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-1911965364719727533759983060186165698250000000000)
      constant := (40509482985010997862461294655316666005111446949157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88181552293392427513/20000000000000000000)
  centralHi := (220453880733481068783/50000000000000000000)
  directionLo := (11093127303081046473/2500000000000000000)
  directionHi := (443725092123241858921/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree080.table
  base := (21188729073617732976846702592075265598011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7736394491671544163379944402877615033000000000000)
      constant := (165924117238029025669141635062034869805226535076379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree080.table
  base := (21188729053353968120194464210027909234823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7744589338970348627520270423346255033000000000000)
      constant := (166270200214808135220723186679820316144645345385447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11093127303081046473/2500000000000000000)
  centralHi := (443725092123241858921/100000000000000000000)
  directionLo := (3488473806955683493/781250000000000000)
  directionHi := (89304929458065497421/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree081.table
  base := (22586990068100446204745382182450576629589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7833019936171747600058528510223349273000000000000)
      constant := (170202957055798768465855688949100380261551742620021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree081.table
  base := (22586990051912176746198261415023113305747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7841317219061787120000608605947847273000000000000)
      constant := (170557742584706802250142855636317887047455820583283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/781250000000000000)
  centralHi := (89304929458065497421/20000000000000000000)
  directionLo := (449306759236630290149/100000000000000000000)
  directionHi := (8986135184732605803/2000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree082.table
  base := (192152384279935328211371000820821100779/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7929645380671951036737112617569083513000000000000)
      constant := (174536962905475526251524717190206875788979905241375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree082.table
  base := (24019048022061439899377727942145490789389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-7938045099153225612480946788549439513000000000000)
      constant := (174900559048493626045924537442607428390275194962221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449306759236630290149/100000000000000000000)
  centralHi := (8986135184732605803/2000000000000000000)
  directionLo := (452071750006229819307/100000000000000000000)
  directionHi := (113017937501557454827/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree083.table
  base := (796403217698774066894072146497614280199/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2006567706293038618353924181228704438250000000000)
      constant := (44731533696516851414770960821503234398181318066488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree083.table
  base := (25484902956034011700998210017001375867651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8034772979244664104961284971151031753000000000000)
      constant := (179298649605197176277791820331071347041055365690339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452071750006229819307/100000000000000000000)
  centralHi := (113017937501557454827/25000000000000000000)
  directionLo := (227409965926994414733/50000000000000000000)
  directionHi := (454819931853988829467/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree084.table
  base := (6746138714009652015919518848712867663811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2030724067418089477523570208065137998250000000000)
      constant := (45842618174200747419025608221037409048260827452579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree084.table
  base := (26984554847792472383610870397841671221209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8131500859336102597441623153752623993000000000000)
      constant := (183752014254062416314749053882612331422830403502201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227409965926994414733/50000000000000000000)
  centralHi := (454819931853988829467/100000000000000000000)
  directionLo := (457551607657146075069/100000000000000000000)
  directionHi := (45755160765714607507/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree085.table
  base := (28518003699244427497158616766406328790301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8219521714172561346772864939606286233000000000000)
      constant := (187869976637084368598226495230142955587381031216189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree085.table
  base := (28518003692660646391509108011449388330443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8228228739427541089921961336354216233000000000000)
      constant := (188260652994504546031325279533087013365217764723627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457551607657146075069/100000000000000000000)
  centralHi := (45755160765714607507/10000000000000000000)
  directionLo := (460267071304922732331/100000000000000000000)
  directionHi := (115066767826230683083/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree086.table
  base := (235041011658503529584091853146189338789/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2079036789668191195862862261738005118250000000000)
      constant := (48106161651612525210636655356182533812948407002272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree086.table
  base := (3008524948703263546889773222439461868419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4162478309759489791201149759477904236500000000000)
      constant := (96412282913036306817132379726610531096247326889455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460267071304922732331/100000000000000000000)
  centralHi := (115066767826230683083/25000000000000000000)
  directionLo := (462966608067561087421/100000000000000000000)
  directionHi := (231483304033780543711/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree087.table
  base := (7921573058084650484418760985362497418787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2103193150793242055032508288574438678250000000000)
      constant := (49258620651136502014290795529421224372832321219843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree087.table
  base := (15843146114071731960224148919264192567609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4210842249805209037441318850778700356500000000000)
      constant := (98721876374210416338006149299684731538377779491801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462966608067561087421/100000000000000000000)
  centralHi := (231483304033780543711/50000000000000000000)
  directionLo := (232825247473053602163/50000000000000000000)
  directionHi := (465650494946107204327/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree088.table
  base := (16660565958618195562835690062196557859731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4254699023836585828404308630821744476500000000000)
      constant := (100849742315551075491412927056448966885496892537459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree088.table
  base := (33321131913888317891970669159581366424511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8518412379701856567362975884158992953000000000000)
      constant := (202118213761285976211522758092766234472971102734879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232825247473053602163/50000000000000000000)
  centralHi := (465650494946107204327/100000000000000000000)
  directionLo := (234159500502075776399/50000000000000000000)
  directionHi := (468319001004151552799/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree089.table
  base := (8747442136337952177221550796844371840089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2151505873043343773371800342247305798250000000000)
      constant := (51604913171478670330399560772477087190972520054521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree089.table
  base := (6997953708536021899453055128270856346627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8615140259793295059843314066760585193000000000000)
      constant := (206847948864469563840749929488884243429757897468015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234159500502075776399/50000000000000000000)
  centralHi := (468319001004151552799/100000000000000000000)
  directionLo := (470972387682652150617/100000000000000000000)
  directionHi := (235486193841326075309/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree090.table
  base := (9173050528867240398953589489110698168429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2175662234168394632541446369083739358250000000000)
      constant := (52798746692207885026194521025448739938626966672781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree090.table
  base := (1834610105666863260985386264981470106741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2177967034971183388080913062340544358250000000000)
      constant := (52908239514455957145872208330310381175714024576745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470972387682652150617/100000000000000000000)
  centralHi := (235486193841326075309/50000000000000000000)
  directionLo := (473610909098882864067/100000000000000000000)
  directionHi := (118402727274720716017/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree091.table
  base := (38428432626695977507543074248175615832291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8799274381173781966844369583680691673000000000000)
      constant := (216025486879741190240911280633845648683746622159299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree091.table
  base := (38428432624995348766514438819601250961413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8808596019976172044803990431963769673000000000000)
      constant := (216473241341240664478690900773137535245745068497957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473610909098882864067/100000000000000000000)
  centralHi := (118402727274720716017/25000000000000000000)
  directionLo := (476234812330474408129/100000000000000000000)
  directionHi := (47623481233047440813/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree092.table
  base := (10049615019598511268309824477882012756611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2223974956418496350880738422756606478250000000000)
      constant := (55227788254640935576598515357405258909133253031779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree092.table
  base := (20099230038518739053871477883186304045267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4452661950033805268642164307282680956500000000000)
      constant := (110684399357321462287459122521590655471199723888563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476234812330474408129/100000000000000000000)
  centralHi := (47623481233047440813/10000000000000000000)
  directionLo := (478844337685446659017/100000000000000000000)
  directionHi := (239422168842723329509/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree093.table
  base := (42002284470121547062379409879402257208017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-8992525270174188840201537798372160153000000000000)
      constant := (225851985185243967876043547486159207898381172723313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree093.table
  base := (42002284469039561043841673804878875875979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9002051780159049029764666797166954153000000000000)
      constant := (226319630177977572118406056714218466429194361114731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478844337685446659017/100000000000000000000)
  centralHi := (239422168842723329509/50000000000000000000)
  directionLo := (481439718959067567627/100000000000000000000)
  directionHi := (120359929739766891907/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree094.table
  base := (43839905801590096340298348558793653620559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9089150714674392276880121905717894393000000000000)
      constant := (230847983379745801402164352014485486625230108434351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree094.table
  base := (43839905800727213470562524114180322900651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9098779660250487522245004979768546393000000000000)
      constant := (231325735731210292773287349570265446395310411827339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481439718959067567627/100000000000000000000)
  centralHi := (120359929739766891907/25000000000000000000)
  directionLo := (96804236735663146409/20000000000000000000)
  directionHi := (242010591839157866023/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree095.table
  base := (11427831018157489359059079997892016278263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2296444039793648928389676503265907158250000000000)
      constant := (58974786900512003963379520185112581119814252587607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree095.table
  base := (914226481438837740093549839383897394087/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4597753770170963007362671581185069316500000000000)
      constant := (118193557687160629279886925959659505250198796038575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804236735663146409/20000000000000000000)
  centralHi := (242010591839157866023/50000000000000000000)
  directionLo := (243294476667335045609/50000000000000000000)
  directionHi := (486588953334670091219/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree096.table
  base := (11904134820790716973095750319470832926193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2320600400918699787559322530102340718250000000000)
      constant := (60251369463035205941780772655818615688154071295377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree096.table
  base := (9523307856522851047243672358319508948373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9292235420433364507205681344971730873000000000000)
      constant := (241503769107301799552460734214911998327072273806985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243294476667335045609/50000000000000000000)
  centralHi := (486588953334670091219/100000000000000000000)
  directionLo := (489143243605900826477/100000000000000000000)
  directionHi := (244571621802950413239/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree097.table
  base := (9911110286636138554218297966931267108889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9379027048175002586915874227755097113000000000000)
      constant := (246166974130023207791834213163484746682300828488605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree097.table
  base := (49555551432743320117443306124166322741713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9388963300524802999686019527573323113000000000000)
      constant := (246675696930151790936007405911318054035337706764657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489143243605900826477/100000000000000000000)
  centralHi := (244571621802950413239/50000000000000000000)
  directionLo := (49168426456749003007/10000000000000000000)
  directionHi := (491684264567490030071/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree098.table
  base := (51528360522728676471506608839673895035491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9475652492675206023594458335100831353000000000000)
      constant := (251383636435700826169088611984690551928778141324099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree098.table
  base := (5152836052238002518495555805670202609631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4742845590308120746083178855087457676500000000000)
      constant := (125951449421438801841534660067247779792684596692795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49168426456749003007/10000000000000000000)
  centralHi := (491684264567490030071/100000000000000000000)
  directionLo := (98842444178853736787/20000000000000000000)
  directionHi := (15444131902945896373/3125000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree099.table
  base := (13383741637973079249458258170563739641251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2393069484293852365068260610611641398250000000000)
      constant := (64163866192296092808900660879357873308838893380739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree099.table
  base := (53534966551614418820102340807193139417159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9582419060707679984646695892776507593000000000000)
      constant := (257185374845490499198203037751655090470565662371751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98842444178853736787/20000000000000000000)
  centralHi := (15444131902945896373/3125000000000000000)
  directionLo := (124181828013204420901/25000000000000000000)
  directionHi := (99345462410563536721/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree100.table
  base := (11115073904157418749493695442862098162041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9668903381675612896951626549792299833000000000000)
      constant := (261982459130488284785804894035914755518063433285245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree100.table
  base := (55575369520565613084299671377744600402733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9679146940799118477127034075378099833000000000000)
      constant := (262523124938005373574942982465495202123874983183437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124181828013204420901/25000000000000000000)
  centralHi := (99345462410563536721/20000000000000000000)
  directionLo := (31201858280321547927/6250000000000000000)
  directionHi := (499229732485144766833/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree101.table
  base := (28824784714775221181219334856973470758633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4882764413087908166815105328569017036500000000000)
      constant := (133682309759814877225428743959196846134881085318537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree101.table
  base := (28824784714686971629678692064027730075541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4887937410445278484803686128989846036500000000000)
      constant := (133958074560219888535960481578107250034702088858549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31201858280321547927/6250000000000000000)
  centralHi := (499229732485144766833/100000000000000000000)
  directionLo := (50171967178411601541/10000000000000000000)
  directionHi := (501719671784116015411/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree102.table
  base := (29878783139167749188415260370498523656091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4931077135338009885154397382241884156500000000000)
      constant := (136400972968313965641200538140534844729185152197499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree102.table
  base := (59757566278194859102324623734434398511139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9872602700981995462087710440581284313000000000000)
      constant := (273364447392813150156318720004919218215325404147971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50171967178411601541/10000000000000000000)
  centralHi := (501719671784116015411/100000000000000000000)
  directionLo := (252098657430544933203/50000000000000000000)
  directionHi := (504197314861089866407/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree103.table
  base := (61899360067306232528236502075098146221303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-9958779715176223206987378871829502553000000000000)
      constant := (278294438381503321377089926734951113182783434094167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree103.table
  base := (30949680033597089054387821656172101670647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-4984665290536716977284024311591438276500000000000)
      constant := (139434009877573114939700014433892895404862160119383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252098657430544933203/50000000000000000000)
  centralHi := (504197314861089866407/100000000000000000000)
  directionLo := (506662842106173091257/100000000000000000000)
  directionHi := (253331421053086545629/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree104.table
  base := (64074950796633680389381081425037483268029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10055405159676426643665962979175236793000000000000)
      constant := (283842096854277314356249783549495897115345756777181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree104.table
  base := (4004684424784025586485831949808199062121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2516514615291218111762096701446117198250000000000)
      constant := (71106716551865147535422974842920474041376526064676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506662842106173091257/100000000000000000000)
  centralHi := (253331421053086545629/50000000000000000000)
  directionLo := (101823285908298358433/20000000000000000000)
  directionHi := (254558214770745896083/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree105.table
  base := (66284338466493031920307498940101895308351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10152030604176630080344547086520971033000000000000)
      constant := (289444921354971819386761584755678136787693873492639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree105.table
  base := (331421692332109592381336128558665093547/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2540696585314077734882181247096515258250000000000)
      constant := (72510246687444571782155793192426103155118750874150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101823285908298358433/20000000000000000000)
  centralHi := (254558214770745896083/50000000000000000000)
  directionLo := (255779124483922978189/50000000000000000000)
  directionHi := (511558248967845956379/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree106.table
  base := (34263761538530698097605800889799158920403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16312384717431527675554625649840000000000000)
      linear := (-1824253479650557763799062156259648500000000000)
      constant := (52528108202849588045379410125518486854295261963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree106.table
  base := (34263761538502376117659439864276112408207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16312384717431527675554625649840000000000000)
      linear := (-1826186226654992778926497538445648500000000000)
      constant := (52636237341068278264178629314698844050525783847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255779124483922978189/50000000000000000000)
  centralHi := (511558248967845956379/100000000000000000000)
  directionLo := (64248558513136668341/12500000000000000000)
  directionHi := (513988468105093346729/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree107.table
  base := (70804504628516095725206796448177584513289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10345281493177036953701715301212439513000000000000)
      constant := (300816068440210988975417646976470973573986236049321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree107.table
  base := (7080450462847098115231090265787856747711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5178121050719593962244700676794622756500000000000)
      constant := (150717525052256380012473645035027598538744697898395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64248558513136668341/12500000000000000000)
  centralHi := (513988468105093346729/100000000000000000000)
  directionLo := (258203625363293675741/50000000000000000000)
  directionHi := (516407250726587351483/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree108.table
  base := (73115283121033375691570161792719641832761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10441906937677240390380299408558173753000000000000)
      constant := (306584391024799870528499171277605995421868114119129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree108.table
  base := (73115283120997446937085011557282046594797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10452969981530626416969739536190837753000000000000)
      constant := (307214992916973921072865115916037973995019502878733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258203625363293675741/50000000000000000000)
  centralHi := (516407250726587351483/100000000000000000000)
  directionLo := (518814756787973740781/100000000000000000000)
  directionHi := (259407378393986870391/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree109.table
  base := (15091971710957487553850010196855608609487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10538532382177443827058883515903907993000000000000)
      constant := (312407879637397415870638084137531411651932223860715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree109.table
  base := (18864964638689706738358581173297452651973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2637424465405516227362519429698107498250000000000)
      constant := (78262552454881728873441212875010595416969938221797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518814756787973740781/100000000000000000000)
  centralHi := (259407378393986870391/50000000000000000000)
  directionLo := (260605571275316482257/50000000000000000000)
  directionHi := (104242228510126592903/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree110.table
  base := (38919115464974863717621791243599848643899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5317578913338823631868733811624821116500000000000)
      constant := (159143267139012532942789503222935455719383351907611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree110.table
  base := (38919115464963472981974153303448443457987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5323212870856751700965207950697011116500000000000)
      constant := (159470350406096615802326740787193197810451247188643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260605571275316482257/50000000000000000000)
  centralHi := (104242228510126592903/20000000000000000000)
  directionLo := (523596560700037571301/100000000000000000000)
  directionHi := (261798280350018785651/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree111.table
  base := (40125200123344209403957880384246506314321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5365891635588925350208025865297688236500000000000)
      constant := (162110177473351926171313845588375641827454257641969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree111.table
  base := (80250400246670280473482840385757302155569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10743153621804941894410754083995614473000000000000)
      constant := (324886465894993938991136788896618252787344057644241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523596560700037571301/100000000000000000000)
  centralHi := (261798280350018785651/50000000000000000000)
  directionLo := (525971160459278433411/100000000000000000000)
  directionHi := (131492790114819608353/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree112.table
  base := (16539273301033610601831902288956719536217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10828408715678054137094635837941110713000000000000)
      constant := (330209341643454352670407554320502736817578075065565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree112.table
  base := (4134818325257680632833156597275029572093/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2709970375474095096722773066649301678250000000000)
      constant := (82721876266987411306942427621269716472729196202385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525971160459278433411/100000000000000000000)
  centralHi := (131492790114819608353/25000000000000000000)
  directionLo := (105667017539599727847/20000000000000000000)
  directionHi := (132083771924499659809/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree113.table
  base := (665438513324603870767740136109288234681/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2731258540044564393443304986321711238250000000000)
      constant := (84063373592074164901038928058583230312178374016288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree113.table
  base := (85176129705537800072131645886493340979549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-10936609381987818879371430449198798953000000000000)
      constant := (336943818331080467078637860496390669415055157390461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105667017539599727847/20000000000000000000)
  centralHi := (132083771924499659809/25000000000000000000)
  directionLo := (265344242518480041139/50000000000000000000)
  directionHi := (530688485036960082279/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree114.table
  base := (171268925484353095563545512263789182667/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2755414901169615252612951013158144798250000000000)
      constant := (85588203280312590577204220467087295037922022676864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree114.table
  base := (87689689847979634628734937295251290434511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11033337262079257371851768631800391193000000000000)
      constant := (343055405684406012859740923689083672552830533624879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265344242518480041139/50000000000000000000)
  centralHi := (530688485036960082279/100000000000000000000)
  directionLo := (533031491948454859041/100000000000000000000)
  directionHi := (266515745974227429521/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree115.table
  base := (90237046932639053046129109422358633182521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11118285049178664447130388159978313433000000000000)
      constant := (348507297902334536311616960726664446198044519991769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree115.table
  base := (90237046932631769989832703275539537954923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11130065142170695864332106814401983433000000000000)
      constant := (349222267127945373360212641806149518454688775414347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533031491948454859041/100000000000000000000)
  centralHi := (266515745974227429521/50000000000000000000)
  directionLo := (107072848970552303933/20000000000000000000)
  directionHi := (267682122426380759833/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree116.table
  base := (3712728038385939900737936950415461991193/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11214910493678867883808972267324047673000000000000)
      constant := (354716948711567740154011697219244603855937977009425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree116.table
  base := (1856364019192854022148642118786823328059/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5613396511131067178406222498501787836500000000000)
      constant := (177722201330858559641435055032826486120008447546275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107072848970552303933/20000000000000000000)
  centralHi := (267682122426380759833/50000000000000000000)
  directionLo := (537686877210834932037/100000000000000000000)
  directionHi := (268843438605417466019/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree117.table
  base := (95433151929161396007694689095005217484689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11311535938179071320487556374669781913000000000000)
      constant := (360981765548968017126710118523012657829469071663921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree117.table
  base := (372785749723268684082227722996936736799/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2830880225588393212323195794901291978250000000000)
      constant := (90430453071434825902049026283626862751454767885504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537686877210834932037/100000000000000000000)
  centralHi := (268843438605417466019/50000000000000000000)
  directionLo := (539999519613407964987/100000000000000000000)
  directionHi := (134999879903351991247/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree118.table
  base := (98081899841317950422362196191738755074767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11408161382679274757166140482015516153000000000000)
      constant := (367301748414552900808745345400522473230146517814063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree118.table
  base := (1532529685020535619998571050778986290539/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2855062195611252835443280340551690038250000000000)
      constant := (92013624000007366908746700121303003454300005993136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539999519613407964987/100000000000000000000)
  centralHi := (134999879903351991247/25000000000000000000)
  directionLo := (542302299866673316273/100000000000000000000)
  directionHi := (271151149933336658137/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree119.table
  base := (20152888939250870729493430705363371257209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11504786827179478193844724589361250393000000000000)
      constant := (373676897308339423412722940640528804203219225531005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree119.table
  base := (20152888939250286566245285606071228677963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11516976662536449834253459544808352393000000000000)
      constant := (374442453804604649725548503481248885196090991704535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542302299866673316273/100000000000000000000)
  centralHi := (271151149933336658137/50000000000000000000)
  directionLo := (272297671537352278929/50000000000000000000)
  directionHi := (544595343074704557859/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree120.table
  base := (6467549155881429531418695107812044887801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2900353067919920407630827174176746158250000000000)
      constant := (95026803057586031539881233958349451581853821574756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree120.table
  base := (51740393247050274284086012555018981782381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-5806852271313944163366898863704972316500000000000)
      constant := (190442842849740697999639107226516024102004877063309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272297671537352278929/50000000000000000000)
  centralHi := (544595343074704557859/100000000000000000000)
  directionLo := (136719692929691699943/25000000000000000000)
  directionHi := (546878771718766799773/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree121.table
  base := (265577313087479855269410690270298349283/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2924509429044971266800473201013179718250000000000)
      constant := (96648173295145767769897859773756206544012549638700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree121.table
  base := (106230925234990093207925794571766437260813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11710432422719326819214135910011536873000000000000)
      constant := (387384191684675772388156233159071648215437833504557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136719692929691699943/25000000000000000000)
  centralHi := (546878771718766799773/100000000000000000000)
  directionLo := (137288176433414810879/25000000000000000000)
  directionHi := (549152705733659243517/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree122.table
  base := (27253715229761566981540807158133807034643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2948665790170022125970119227849613278250000000000)
      constant := (98283335039767963443615836276964211946627058877427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree122.table
  base := (109014860919044797059788837816453103512829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11807160302810765311694474092613129113000000000000)
      constant := (393937971760203377600926567287702866436278499684381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137288176433414810879/25000000000000000000)
  centralHi := (549152705733659243517/100000000000000000000)
  directionLo := (551417262581224268539/100000000000000000000)
  directionHi := (27570863129061213427/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree123.table
  base := (27958148386596733153928681658903952365377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-2972822151295072985139765254686046838250000000000)
      constant := (99932288291456404194863557067131538133269388912353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree123.table
  base := (111832593546385762567177304721743087189033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11903888182902203804174812275214721353000000000000)
      constant := (400547025926079356647279491956971414705892913384137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551417262581224268539/100000000000000000000)
  centralHi := (27570863129061213427/5000000000000000000)
  directionLo := (553672557321150535953/100000000000000000000)
  directionHi := (276836278660575267977/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree124.table
  base := (114684123117131505486155008900551918925877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-11987914049680495377237645126089921593000000000000)
      constant := (406380132200859063252361785324040568060839606496853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree124.table
  base := (22936824623426114958894637418467592136921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12000616062993642296655150457816313593000000000000)
      constant := (407211354182318414655280651162775459465518791466845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553672557321150535953/100000000000000000000)
  centralHi := (276836278660575267977/50000000000000000000)
  directionLo := (555918702679190869863/100000000000000000000)
  directionHi := (69489837834898858733/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree125.table
  base := (58784724815697076445214098581704387003743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6042269747090349406958114616717827916500000000000)
      constant := (206543138632093235389473100892133101668996340667327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree125.table
  base := (2939236240784835315962653988709418639121/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3024335985771270197283872160104476458250000000000)
      constant := (103482739132233707694855536933286463965267976691690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555918702679190869863/100000000000000000000)
  centralHi := (69489837834898858733/12500000000000000000)
  directionLo := (3488473806955683493/625000000000000000)
  directionHi := (558155809112909358881/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree126.table
  base := (12048857308928574828783977427432350926297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6090582469340451125297406670390695036500000000000)
      constant := (209923794177910852568685941814669735996056897411165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree126.table
  base := (24097714617857031909047755975302721648213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12194071823176519281615826823019498073000000000000)
      constant := (420705832965942472046794618258014544963673777715785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/625000000000000000)
  centralHi := (558155809112909358881/100000000000000000000)
  directionLo := (280191992437533090447/50000000000000000000)
  directionHi := (112076796975013236179/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree127.table
  base := (123441493490913981038518593565442238842189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12277790383181105687273397448127124313000000000000)
      constant := (426664065475778233903987282231134514332120107981421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree127.table
  base := (61720746745456756412457675707416150181251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6145399851633978887048082502810545156500000000000)
      constant := (213767991746677403513991944889001637496889507440739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280191992437533090447/50000000000000000000)
  centralHi := (112076796975013236179/20000000000000000000)
  directionLo := (562603336074743067527/100000000000000000000)
  directionHi := (70325417009342883441/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree128.table
  base := (2528564216727669264777897197419714764971/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6187207913840654561975990777736429276500000000000)
      constant := (216767854312034569907057588865192155127825708995475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree128.table
  base := (12642821083638309090234669215472613004567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6193763791679698133288251594111341276500000000000)
      constant := (217210704055592459624868394056393849731229518431315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562603336074743067527/100000000000000000000)
  centralHi := (70325417009342883441/12500000000000000000)
  directionLo := (282406983368153533677/50000000000000000000)
  directionHi := (112962793347261413471/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree129.table
  base := (129448725125795834102342843057724921078213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12471041272181512560630565662818592793000000000000)
      constant := (440462517800707133815842518282375328297106646813157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree129.table
  base := (64724362562897769013989790998302230370807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6242127731725417379528420685412137396500000000000)
      constant := (220681053409722760145036987789204242126858403937623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282406983368153533677/50000000000000000000)
  centralHi := (112962793347261413471/20000000000000000000)
  directionLo := (141753994714076329279/25000000000000000000)
  directionHi := (567015978856305317117/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree130.table
  base := (66251518179624930769864645247779306164621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6283833358340857998654574885082163516500000000000)
      constant := (223722246502852283886815948430139604746222052138669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree130.table
  base := (66251518179624813060816360633528421995211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6290491671771136625768589776712933516500000000000)
      constant := (224179039809074481257407763905176525897947448107179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141753994714076329279/25000000000000000000)
  centralHi := (567015978856305317117/100000000000000000000)
  directionLo := (569209472458378867513/100000000000000000000)
  directionHi := (284604736229189433757/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree131.table
  base := (33897786134210385177696018994759500603973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3166073040295479858496933469377515318250000000000)
      constant := (113620408559768361698276401214719254174803054749797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree131.table
  base := (13559114453684135353347982297501477361153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6338855611816855872008758868013729636500000000000)
      constant := (227704663253653625714289506209375513571029313154085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569209472458378867513/100000000000000000000)
  centralHi := (284604736229189433757/50000000000000000000)
  directionLo := (142848636411569804009/25000000000000000000)
  directionHi := (571394545646279216037/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree132.table
  base := (138713049658664189406398559918972688774119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12760917605682122870666317984855795513000000000000)
      constant := (461573941500825441149507124665659428249047358565191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree132.table
  base := (34678262414666010148319173632067817785997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3193609775931287559124463979657262878250000000000)
      constant := (115628961871733014406029250543200855045911896175533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142848636411569804009/25000000000000000000)
  centralHi := (571394545646279216037/100000000000000000000)
  directionLo := (22942851786202682251/4000000000000000000)
  directionHi := (143392823663766764069/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree133.table
  base := (28373750344961708038002059144479324506941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12857543050182326307344902092201529753000000000000)
      constant := (468721414790971897810855616793120319076016092065745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree133.table
  base := (141868751724808421884671366441446959252389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12871166983816588728978194101230643753000000000000)
      constant := (469677642557034728322095147524525093019957590369221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22942851786202682251/4000000000000000000)
  centralHi := (143392823663766764069/25000000000000000000)
  directionLo := (35983738368785552819/6250000000000000000)
  directionHi := (115147962780113769021/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree134.table
  base := (145058250735362829277755769703325986870251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-12954168494682529744023486199547263993000000000000)
      constant := (475924054109523851553252403773946046585414299361739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree134.table
  base := (2901165014707254704623931032074754775281/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6483947431954013610729266141916117996500000000000)
      constant := (238447355858813149249817460861311299314673792285225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35983738368785552819/6250000000000000000)
  centralHi := (115147962780113769021/20000000000000000000)
  directionLo := (72237524503395387631/12500000000000000000)
  directionHi := (577900196027163101049/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree135.table
  base := (148281546690412882175689762618417971386083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13050793939182733180702070306892998233000000000000)
      constant := (483181859456492035670627862895571192257460161691587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree135.table
  base := (18535193336301600927219405848779507499217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3266155685999866428484717616608457058250000000000)
      constant := (121041763742179375402649701614589411693984991840226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72237524503395387631/12500000000000000000)
  centralHi := (577900196027163101049/100000000000000000000)
  directionLo := (145013132988491216283/25000000000000000000)
  directionHi := (580052531953964865133/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree136.table
  base := (37884659897510549030232681449317322998019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3286854845920734154345163603559683118250000000000)
      constant := (122623707707971723071197234878436622989980204152291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree136.table
  base := (151538639590042136698850810957074509365801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13161350624090904206419208649035420473000000000000)
      constant := (491494672310318779904027383751567752134212787135689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145013132988491216283/25000000000000000000)
  centralHi := (580052531953964865133/100000000000000000000)
  directionLo := (291098455459736733297/50000000000000000000)
  directionHi := (116439382183894693319/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree137.table
  base := (154829529434332019394336399912607489833717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13244044828183140054059238521584466713000000000000)
      constant := (497862968235718582264221831158697768224677342990613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree137.table
  base := (77414764717165986082332379268965934806677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6629039252091171349449773415818506356500000000000)
      constant := (249438781871220147174810234357287453831455339408053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291098455459736733297/50000000000000000000)
  centralHi := (116439382183894693319/20000000000000000000)
  directionLo := (584333420524745627939/100000000000000000000)
  directionHi := (29216671026237281397/5000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree138.table
  base := (15815421622336142758700222694935395998187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6670335136341671745368911314465100476500000000000)
      constant := (252643135833998497380970653377644218212229555732215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree138.table
  base := (158154216223361390050062181532666511568633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13354806384273781191379885014238604953000000000000)
      constant := (506315729265091934180902333736819389290685831408537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584333420524745627939/100000000000000000000)
  centralHi := (29216671026237281397/5000000000000000000)
  directionLo := (146615536693788251459/25000000000000000000)
  directionHi := (586462146775153005837/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree139.table
  base := (161512699957207396912887712138646697707811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13437295717183546927416406736275935193000000000000)
      constant := (512764741128731756383930296694417441136376314968579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree139.table
  base := (1292101599657658936648401678737200138767/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13451534264365219683860223196840197193000000000000)
      constant := (513809168878283326067892323494060817731366263757875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146615536693788251459/25000000000000000000)
  centralHi := (586462146775153005837/100000000000000000000)
  directionLo := (588583174120780485673/100000000000000000000)
  directionHi := (294291587060390242837/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree140.table
  base := (164904980635944874666295361967932842233509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13533921161683750364094990843621669433000000000000)
      constant := (520298376617932240000516205048824106506040254216901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree140.table
  base := (16490498063594485095918250320272254230539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6774131072228329088170280689720894716500000000000)
      constant := (260678941291011921465924231589502883772246477672855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588583174120780485673/100000000000000000000)
  centralHi := (294291587060390242837/50000000000000000000)
  directionLo := (590696585495518918633/100000000000000000000)
  directionHi := (295348292747759459317/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree141.table
  base := (168331058259646846926600862255816268774843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13630546606183953800773574950967403673000000000000)
      constant := (527887178135607573213489868526007579861368521635227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree141.table
  base := (168331058259646828087716768804573325444133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13644990024548096668820899562043381673000000000000)
      constant := (528961870376322612415066109588170930772323971028037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590696585495518918633/100000000000000000000)
  centralHi := (295348292747759459317/50000000000000000000)
  directionLo := (592802462354903501801/100000000000000000000)
  directionHi := (296401231177451750901/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree142.table
  base := (34358186565676880722844942221313629813621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13727172050684157237452159058313137913000000000000)
      constant := (535531145681766646491972125284013482657133037498345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree142.table
  base := (42947733207096097161159254739762626891989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3435429476159883790325309436161243478250000000000)
      constant := (134155283065297131254719215587845803701284802533621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592802462354903501801/100000000000000000000)
  centralHi := (296401231177451750901/50000000000000000000)
  directionLo := (297450442356373322761/50000000000000000000)
  directionHi := (594900884712746645523/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree143.table
  base := (17528460434222680100186209076388501670469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6911898747592180337065371582829436076500000000000)
      constant := (271615139628209060495018139733500188427672497651705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree143.table
  base := (87642302171113394553725182191714179412979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-6919222892365486826890787963623283076500000000000)
      constant := (272167834118315120961483850364405681670316473707731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297450442356373322761/50000000000000000000)
  centralHi := (594900884712746645523/100000000000000000000)
  directionLo := (119398386235322388057/20000000000000000000)
  directionHi := (298495965588305970143/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree144.table
  base := (35762414560248304356770505061786197217961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13920422939684564110809327273004606393000000000000)
      constant := (550984578859570436058952775149061841128657121409645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree144.table
  base := (35762414560248302466670181100457433271773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-13935173664822412146261914109848158393000000000000)
      constant := (552105478302656202498975578893368070128097647519985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119398386235322388057/20000000000000000000)
  centralHi := (298495965588305970143/50000000000000000000)
  directionLo := (599075678982173720199/100000000000000000000)
  directionHi := (2995378394910868601/500000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree145.table
  base := (182373338205494332804587198377147478477309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14017048384184767547487911380350340633000000000000)
      constant := (558794044491231816466674316271751341908510761635101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree145.table
  base := (182373338205494325296214660082520264918641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14031901544913850638742252292449750633000000000000)
      constant := (559930562459274631531046507976335936729119870034449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599075678982173720199/100000000000000000000)
  centralHi := (2995378394910868601/500000000000000000)
  directionLo := (601152204026504715043/100000000000000000000)
  directionHi := (150288051006626178761/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree146.table
  base := (185968400555049340544262455072609195366393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14113673828684970984166495487696074873000000000000)
      constant := (566658676151410279336855846373452113182222276353177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree146.table
  base := (46492100138762333644796169675690910091221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3532157356251322282805647618762835718250000000000)
      constant := (141952730176623386538927473474245083463078041646069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601152204026504715043/100000000000000000000)
  centralHi := (150288051006626178761/25000000000000000000)
  directionLo := (603221580900332381179/100000000000000000000)
  directionHi := (30161079045016619059/5000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree147.table
  base := (189597259849969044457280468619273320302661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14210299273185174420845079595041809113000000000000)
      constant := (574578473840113640819327680038041722881884110000229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree147.table
  base := (94798629924984519859253015909150821617373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7112678652548363811851464328826467556500000000000)
      constant := (287873276522160381266515641072604059862773820902397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603221580900332381179/100000000000000000000)
  centralHi := (30161079045016619059/5000000000000000000)
  directionLo := (302641941459651348789/50000000000000000000)
  directionHi := (605283882919302697579/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree148.table
  base := (96629958045157194127658164462219572673837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7153462358842688928761831851193771676500000000000)
      constant := (291276718778674761251764833671678038921388418889293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree148.table
  base := (96629958045157192245457717203546017104719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7161042592594083058091633420127263676500000000000)
      constant := (291868729736381951130293548191850669081601417628591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302641941459651348789/50000000000000000000)
  centralHi := (605283882919302697579/100000000000000000000)
  directionLo := (24293567286171540039/4000000000000000000)
  directionHi := (37958698884643031311/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree149.table
  base := (98478184638072404611812522259400591161797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7201775081092790647101123904866638796500000000000)
      constant := (295291783651562678792991673445467237264242249141733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree149.table
  base := (196956369276144806233386232352757697387193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14418813065279604608663605022856119593000000000000)
      constant := (591783639991830398541366744055286120519308991724377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24293567286171540039/4000000000000000000)
  centralHi := (37958698884643031311/6250000000000000000)
  directionLo := (304693774730388904303/50000000000000000000)
  directionHi := (609387549460777808607/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree150.table
  base := (200686619407518285655635655574322847308541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14500175606685784730880831917079011833000000000000)
      constant := (598668863077448396802438046502443129880431162795549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree150.table
  base := (200686619407518283280456786283614908646567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14515540945371043101143943205457711833000000000000)
      constant := (599885094601527502116260663591037419185621350624263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304693774730388904303/50000000000000000000)
  centralHi := (609387549460777808607/100000000000000000000)
  directionLo := (76428631813422004137/12500000000000000000)
  directionHi := (611429054507376033097/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree151.table
  base := (102225333242245691243667841367008715467861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7298400525592994083779708012212373036500000000000)
      constant := (303404662440162857067441841609937118722707092583029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree151.table
  base := (204450666484491380600789382919674732398413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14612268825462481593624281388059304073000000000000)
      constant := (608041823301862286971345061581731303951707274190957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76428631813422004137/12500000000000000000)
  centralHi := (611429054507376033097/100000000000000000000)
  directionLo := (153365941450863631809/25000000000000000000)
  directionHi := (613463765803454527237/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree152.table
  base := (208248510507119295209434170678588827420811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14693426495686191604238000131770480313000000000000)
      constant := (615004952711764212303183434418674794394355811625579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree152.table
  base := (13015531906694955856941402501146088468479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3677249176388480021526154892665224078250000000000)
      constant := (154063456523210413957432707982359193914367105388924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153365941450863631809/25000000000000000000)
  centralHi := (613463765803454527237/100000000000000000000)
  directionLo := (30774587536298825117/5000000000000000000)
  directionHi := (615491750725976502341/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree153.table
  base := (42416030295091178426367957670848735951573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14790051940186395040916584239116214553000000000000)
      constant := (623255746571770628050647771873927571988498240630985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree153.table
  base := (4241603029509117818836471501964460285737/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7402862292822679289292478876631244276500000000000)
      constant := (312260551487236172718654771385599953267501580209825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30774587536298825117/5000000000000000000)
  centralHi := (615491750725976502341/100000000000000000000)
  directionLo := (154378268886382509609/25000000000000000000)
  directionHi := (617513075545530038437/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree154.table
  base := (1687074917105888711497080347200006399863/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3721669346171649619398792086615487198250000000000)
      constant := (157890426615087884308112657517736296366485086400224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree154.table
  base := (215945589389553754126548322255943724181051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14902452465736797071065295935864080793000000000000)
      constant := (632843653946760931651306327495145094373339181542939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154378268886382509609/25000000000000000000)
  centralHi := (617513075545530038437/100000000000000000000)
  directionLo := (619527805451596644039/100000000000000000000)
  directionHi := (15488195136289916101/2500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree155.table
  base := (219844824249464218532398018112273473754291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14983302829186801914273752453807683033000000000000)
      constant := (639922832377513359715380838825902048433466544017299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree155.table
  base := (219844824249464217781874882828588931833569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-14999180345828235563545634118465673033000000000000)
      constant := (641221479009713834340140021558367854614911972186241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619527805451596644039/100000000000000000000)
  centralHi := (15488195136289916101/2500000000000000000)
  directionLo := (310768002288541312003/50000000000000000000)
  directionHi := (621536004577082624007/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree156.table
  base := (11188892802761870371991226239177986614421/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3769982068421751337738084140288354318250000000000)
      constant := (162084781080815591024257198305238215409741651454345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree156.table
  base := (223777856055237406843829742219293518419867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15095908225919674056025972301067265273000000000000)
      constant := (649654578163337322102696254915850194497600654467963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310768002288541312003/50000000000000000000)
  centralHi := (621536004577082624007/100000000000000000000)
  directionLo := (623537736022139372667/100000000000000000000)
  directionHi := (155884434005534843167/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree157.table
  base := (28468085600865284186886492821404913266691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3794138429546802196907730167124787878250000000000)
      constant := (164202645574401168063032628095685114655068394361798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree157.table
  base := (1779255350054080257983034902016920909023/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3798159026502778137126577620917214378250000000000)
      constant := (164535737851909379203685053717255679297859119815904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623537736022139372667/100000000000000000000)
  centralHi := (155884434005534843167/25000000000000000000)
  directionLo := (625533061877297622907/100000000000000000000)
  directionHi := (156383265469324405727/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree158.table
  base := (231745310504566630205124114015175506687567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15273179162687412224309504775844885753000000000000)
      constant := (665337206300546263713429190021216607230663211673263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree158.table
  base := (115872655252283314914666761430881189472191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7644681993051275520493324333135224876500000000000)
      constant := (333343299371310199004916405912997348490854386170399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625533061877297622907/100000000000000000000)
  centralHi := (156383265469324405727/25000000000000000000)
  directionLo := (627522043245939647191/100000000000000000000)
  directionHi := (78440255405742455899/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree159.table
  base := (117889866574108593322829138372910150365461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (16312384717431527675554625649840000000000000)
      linear := (-2735814276822288298502685810464688500000000000)
      constant := (119957101518706475595241756385318120554420689181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree159.table
  base := (58944933287054296586819275084355679756579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (8156192358715763837777312824920000000000000)
      linear := (-1369356698664470410596919441871844250000000000)
      constant := (60100170894294393654482652665570307155942653659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627522043245939647191/100000000000000000000)
  centralHi := (78440255405742455899/12500000000000000000)
  directionLo := (314752370133066210427/50000000000000000000)
  directionHi := (125900948053226484171/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree160.table
  base := (29980994092239947501327324572792403360539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3866607512921954774416668247634088558250000000000)
      constant := (170638988098062632039549763629834587354701780209142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree160.table
  base := (239847952737919579773710575315413726586549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15482819746285428025947325031473634233000000000000)
      constant := (683939715684657451455210732249138864750499532213461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314752370133066210427/50000000000000000000)
  centralHi := (125900948053226484171/20000000000000000000)
  directionLo := (157870303032960954689/25000000000000000000)
  directionHi := (631481212131843818757/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree161.table
  base := (48789993854743681399742628492408109151787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15563055496188022534345257097882088473000000000000)
      constant := (691248074481024485746173309522556595770393528284215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree161.table
  base := (121974984636859203405310393129694717468767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7789773813188433259213831607037613236500000000000)
      constant := (346324592645861454155462655912678748049768374480063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157870303032960954689/25000000000000000000)
  centralHi := (631481212131843818757/100000000000000000000)
  directionLo := (633451517113563021123/100000000000000000000)
  directionHi := (158362879278390755281/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree162.table
  base := (124042891377828627042891530434040623528041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7829840470344112985511920602613911356500000000000)
      constant := (349997681299210151780193478503364850284158184631049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree162.table
  base := (248085782755657253936453504014481298961843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15676275506468305010908001396676818713000000000000)
      constant := (701413928989493628571632561695107103136724316078227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633451517113563021123/100000000000000000000)
  centralHi := (158362879278390755281/25000000000000000000)
  directionLo := (635415712578345450773/100000000000000000000)
  directionHi := (317707856289172725387/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree163.table
  base := (252255393183778726729152798191555621525341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15756306385188429407702425312573556953000000000000)
      constant := (708797816744443309817561603544735809964536546010749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree163.table
  base := (126127696591889363305301084943097193850771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7886501693279871751694169789639205476500000000000)
      constant := (355116973388987470227156417939002821341686363516019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635415712578345450773/100000000000000000000)
  centralHi := (317707856289172725387/50000000000000000000)
  directionLo := (39835865938081359359/6250000000000000000)
  directionHi := (127474771001860349949/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree164.table
  base := (400716875872069496168848325624984048059/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3963232957422158211095252354979822798250000000000)
      constant := (179413859229774678393243746721255110829845597096160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree164.table
  base := (128229400279062238726975399446548557597607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-7934865633325590997934338880940001596500000000000)
      constant := (359554619328586026507224700010271803055343799042823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39835865938081359359/6250000000000000000)
  centralHi := (127474771001860349949/20000000000000000000)
  directionLo := (79915750003068690823/12500000000000000000)
  directionHi := (127865200004909905317/20000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree165.table
  base := (65174001219683808380551969329851868844757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4252022626)
      previous := (2126011313)
      next := (2126011313)
      square := (22910744335632580620316471725200280000000000000)
      linear := (-3987389318547209070264898381816256358250000000000)
      constant := (181642055780597902030474051324383632509045330749173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree165.table
  base := (260696004878735233447499174402838355980809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-15966459146742620488349015944481595433000000000000)
      constant := (728039804627090059547474599739789860799810067346601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79915750003068690823/12500000000000000000)
  centralHi := (127865200004909905317/20000000000000000000)
  directionLo := (320636101197822932137/50000000000000000000)
  directionHi := (25650888095825834571/4000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree166.table
  base := (132483503072825411124222436304516067487627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-8023091359344519858869088817305379836500000000000)
      constant := (367768087677163487141618160839648611053792146442603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree166.table
  base := (132483503072825411094570650991041364194349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-8031593513417029490414677063541593836500000000000)
      constant := (368512822343866970436214578424037319676758182627661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320636101197822932137/50000000000000000000)
  centralHi := (25650888095825834571/4000000000000000000)
  directionLo := (321606258032758935549/50000000000000000000)
  directionHi := (643212516065517871099/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree167.table
  base := (53854360871782039458776604397830895206303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-16142808163189243154416761741956493913000000000000)
      constant := (744559293614909683570192728249054030218064013795835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree167.table
  base := (26927180435891019724680971262263549111649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-8079957453462748736654846154842389956500000000000)
      constant := (373033379419554284251306720228854885306021139436805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321606258032758935549/50000000000000000000)
  centralHi := (643212516065517871099/100000000000000000000)
  directionLo := (645146994165907881051/100000000000000000000)
  directionHi := (161286748541476970263/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree168.table
  base := (273610399518551462681797799214340098234063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-16239433607689446591095345849302228153000000000000)
      constant := (753637577904144501252445099860783839681361721173807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree168.table
  base := (273610399518551462644433826152105239868939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (17008090504)
      previous := (8504045252)
      next := (8504045252)
      square := (91642977342530322481265886900801120000000000000)
      linear := (-16256642787016935965790030492286372153000000000000)
      constant := (755163147081218707707788907584402453646231938312171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell135.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645146994165907881051/100000000000000000000)
  centralHi := (161286748541476970263/25000000000000000000)
  directionLo := (323537844517174632483/50000000000000000000)
  directionHi := (647075689034349264967/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree169.table
  base := (138991395812305948272570878801224325769967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-8168029526094825013886964978323981196500000000000)
      constant := (381385514111018044657125678446831716447411604566863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree169.table
  base := (138991395812305948257742762323826929831473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (8504045252)
      previous := (4252022626)
      next := (4252022626)
      square := (45821488671265161240632943450400560000000000000)
      linear := (-8176685333554187229135184337443982196500000000000)
      constant := (382157404707034510236139212798295406183287869497297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell135.Kernel169
