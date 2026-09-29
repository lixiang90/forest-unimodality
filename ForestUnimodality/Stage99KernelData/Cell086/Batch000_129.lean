import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell086.Parameters
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch000_049
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch050_099
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch100_149
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch000_049
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch050_099
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree000.table
  base := (998169540640085527294189647/20000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18978711430692582484702768400000000000)
      linear := (-672117831548927832652218220000000000)
      constant := (9981695406400855272941896470000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree000.table
  base := (998169540640085527294189647/20000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18978711430692582484702768400000000000)
      linear := (-672117831548927832652218220000000000)
      constant := (9981695406400855272941896470000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree001.table
  base := (139242987634077575019910618670253991696737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-229859344115084232289093505864839645500000000000)
      constant := (63358952642506370516866448081729458412624848711217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree001.table
  base := (69558985398442657881914320636572753552041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-230112247306592855133566223192999895500000000000)
      constant := (63302256693699442443778743669317173543874907237362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49975232767290864339/100000000000000000000)
  directionHi := (2498761638364543217/5000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree002.table
  base := (81731054010763698308078289363057366041811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-452080320429880953270380767772688115500000000000)
      constant := (37390538337160608799172140622258635705968661149251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree002.table
  base := (40800602750012385067476664103781028165029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-452586126812898198959326202429008615500000000000)
      constant := (37332041531207606863998428199102370602843725462378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49975232767290864339/100000000000000000000)
  centralHi := (2498761638364543217/5000000000000000000)
  directionLo := (14135130392451008451/20000000000000000000)
  directionHi := (4417228247640940141/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree003.table
  base := (4074179078255174880374848871559243717767/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (1917208514188568059378775521317223200000000000)
      linear := (-5993789304397134882237049152715880760000000000)
      constant := (210468551004600910825652853794506690021122680383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree003.table
  base := (25411800788431114484294627501857397689727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-75006667368800393642787353518335259500000000000)
      constant := (2625754094565806576183394745421889173763967460846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14135130392451008451/20000000000000000000)
  centralHi := (4417228247640940141/6250000000000000000)
  directionLo := (43279821136514379971/50000000000000000000)
  directionHi := (86559642273028759943/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree004.table
  base := (3377260276480175101959075259680919000551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-179304454611894879046591058317677011100000000000)
      constant := (3256815121097320816986093916137587928966310715182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree004.table
  base := (67392905662781227324616734773288153472369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-1795067771651017773221692321802052111000000000000)
      constant := (32503125221209135091920274892536625575051154232129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43279821136514379971/50000000000000000000)
  centralHi := (86559642273028759943/100000000000000000000)
  directionLo := (49975232767290864339/50000000000000000000)
  directionHi := (99950465534581728679/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree005.table
  base := (47407716384871150499901435616213658099883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-2237486498748542232428485106992467051000000000000)
      constant := (24452112673418902601575570709121664099595295650203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree005.table
  base := (11824429692613101435064849276159587733757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-1120007765331814230436606140137034775500000000000)
      constant := (12204336019122572963131849431686355214986045858074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49975232767290864339/50000000000000000000)
  centralHi := (99950465534581728679/100000000000000000000)
  directionLo := (55874008829518650603/50000000000000000000)
  directionHi := (111748017659037301207/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree006.table
  base := (34802592643754000364028437401780767502551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-297992050153126186043451070089795999000000000000)
      constant := (2221014307719539968823058918363763824350957104399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree006.table
  base := (6944349105082557438709570830123349525017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (9586042570942840296893877606586116000000000000)
      linear := (-59665850881694203300549605305468599800000000000)
      constant := (443595918343080157883996245707514399343020385633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55874008829518650603/50000000000000000000)
  centralHi := (111748017659037301207/100000000000000000000)
  directionLo := (24482764011336150617/20000000000000000000)
  directionHi := (61206910028340376543/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree007.table
  base := (1646401223377432515470742988079892995303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-1563185202003864558176817077311930465500000000000)
      constant := (8819665717108484586204435222920331910613416499384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree007.table
  base := (13140407427143874456243147079380202882469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-1564955524344424918088126098609052215500000000000)
      constant := (8812082268324250863150710867805645887915488546229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/20000000000000000000)
  centralHi := (61206910028340376543/50000000000000000000)
  directionLo := (66111018807408946019/50000000000000000000)
  directionHi := (132222037614817892039/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree008.table
  base := (20273681587576761328759682633550290495587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-3570812356637322558316208678439557871000000000000)
      constant := (16605598712109311029373767772984951968498326714067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree008.table
  base := (5056181360799457885116052667477138374689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-1787429403850730261913886077845060935500000000000)
      constant := (8300050667923340945072925099961888773241344854498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66111018807408946019/50000000000000000000)
  centralHi := (132222037614817892039/100000000000000000000)
  directionLo := (141351303924510084511/100000000000000000000)
  directionHi := (4417228247640940141/3125000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree009.table
  base := (3917191128577478918457025543923337298891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-24785520427573555557276439520094165500000000000)
      constant := (101643525170525102563677569371285291907362826902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree009.table
  base := (7814167908466353861008714335420418829851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-24813620782185624762217852556556415500000000000)
      constant := (101660933627122595381518598008392935160555418011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141351303924510084511/100000000000000000000)
  centralHi := (4417228247640940141/3125000000000000000)
  directionLo := (149925698301872593017/100000000000000000000)
  directionHi := (74962849150936296509/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree010.table
  base := (12021247847774738660268493592658261410403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-4459696261896509442241357726070951751000000000000)
      constant := (16991077344070219274520523767458171447236765581523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree010.table
  base := (2996712607021167718411100881226356248921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-2232377162863340949565406036317078375500000000000)
      constant := (8500800883637543835152445087851610951392717981522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149925698301872593017/100000000000000000000)
  centralHi := (74962849150936296509/50000000000000000000)
  directionLo := (39508890535429668833/25000000000000000000)
  directionHi := (158035562141718675333/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree011.table
  base := (9042446560053234936075922468567090941327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-4904138214526102884203932249886648691000000000000)
      constant := (18048845616192580945259067817270631765313862889407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree011.table
  base := (901257930135536161491555475662205936953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-490970208473929258678233203110617419100000000000)
      constant := (1806691333567406985945716665689548503600222920073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39508890535429668833/25000000000000000000)
  centralHi := (158035562141718675333/100000000000000000000)
  directionLo := (165749095899778371993/100000000000000000000)
  directionHi := (82874547949889185997/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree012.table
  base := (6558573258605383876203827822435998964221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-594286685239521814018500752633593959000000000000)
      constant := (2173394971669895917505973537459562183447373424229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree012.table
  base := (1633079278878665800294381804153897850687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-297480546875105737468547332754343979500000000000)
      constant := (1088126078040999790469989463309454527280969282926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165749095899778371993/100000000000000000000)
  centralHi := (82874547949889185997/50000000000000000000)
  directionLo := (34623856909211503977/20000000000000000000)
  directionHi := (86559642273028759943/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree013.table
  base := (4458320463516137433463726586159405090103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-5793022119785289768129081297518042571000000000000)
      constant := (21475606015258877418356459316811874050920080949223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree013.table
  base := (887017275789320845194648278230358576637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-1159919520552902792417074389610041814200000000000)
      constant := (4301844253378108651850740413647235414605232287117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34623856909211503977/20000000000000000000)
  centralHi := (86559642273028759943/50000000000000000000)
  directionLo := (180188264245715327139/100000000000000000000)
  directionHi := (9009413212285766357/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree014.table
  base := (666448482753150749664759905833418089483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-3118732036207441605045827910666869755500000000000)
      constant := (11879749519482429523113468176258141532255542447606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree014.table
  base := (529035271316865009073615938889640710929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-1248909072355424929947378381304445302200000000000)
      constant := (4760270390905440484571915661268246213852928613089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180188264245715327139/100000000000000000000)
  centralHi := (9009413212285766357/5000000000000000000)
  directionLo := (93495099419740491329/50000000000000000000)
  directionHi := (186990198839480982659/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree015.table
  base := (1126259132154217121536921309691593591337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-742434002782719628006025593905492939000000000000)
      constant := (2931928035340494046507655739530567524730363043313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree015.table
  base := (44318167175423116984345981454173629813/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (1917208514188568059378775521317223200000000000)
      linear := (-29731080536843268166170719399974417560000000000)
      constant := (117501449700597581786855159815123067192184603037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93495099419740491329/50000000000000000000)
  centralHi := (186990198839480982659/100000000000000000000)
  directionLo := (1209707776440979489/625000000000000000)
  directionHi := (193553244230556718241/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree016.table
  base := (-201583574763114290659409873176637452017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-7126347977674070094016804868965133391000000000000)
      constant := (29340391653240298612358655897013983999632716522303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree016.table
  base := (-108911145504277355362362497830248647753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-3567220439901173012519965911733130695500000000000)
      constant := (14699947946027743739259505549258036375421007937127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1209707776440979489/625000000000000000)
  centralHi := (193553244230556718241/100000000000000000000)
  directionLo := (199900931069163457357/100000000000000000000)
  directionHi := (99950465534581728679/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree017.table
  base := (-1349955538106099159248657150421213371589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-7570789930303663535979379392780830331000000000000)
      constant := (32603969701524060424148511596561179361706466199851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree017.table
  base := (-682169955850197778422810855582797141093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-3789694319407478356345725890969139415500000000000)
      constant := (16336464709517388324117949456680817968721555810187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199900931069163457357/100000000000000000000)
  centralHi := (99950465534581728679/50000000000000000000)
  directionLo := (206053163364369008517/100000000000000000000)
  directionHi := (103026581682184504259/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree018.table
  base := (-18756685183807481252888887511147069811/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (22448644)
      previous := (11224322)
      next := (11224322)
      square := (213023168243174228819863946813024800000000000)
      linear := (-3958139201448521964415779711899519640000000000)
      constant := (17859945923137873785624874008731092067712142145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree018.table
  base := (-294663081899737477650681053993505578739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-49532940727330662965080072471668495500000000000)
      constant := (223736056870406479755479090572620818950874220084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206053163364369008517/100000000000000000000)
  centralHi := (103026581682184504259/50000000000000000000)
  directionLo := (106013477943382563383/50000000000000000000)
  directionHi := (212026955886765126767/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree019.table
  base := (-3206339202601990087335756274558893966219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-8459673835562850419904528440412224211000000000000)
      constant := (40018168979279626196731066959648955355951683270021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree019.table
  base := (-3217564527301034646051261875765695149007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-8469284156840178087994491698882313711000000000000)
      constant := (40107354082397360393817121266553606728295151795713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106013477943382563383/50000000000000000000)
  centralHi := (212026955886765126767/100000000000000000000)
  directionLo := (108918494656271700083/50000000000000000000)
  directionHi := (217836989312543400167/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree020.table
  base := (-39523093778207132947322589433674416987/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8627438313848556267204489845927504400000000000)
      linear := (-178082315763848877237342059284558423020000000000)
      constant := (883030697085238464652955107509288412146627017066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree020.table
  base := (-9905495230838198407432569462594031071/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8627438313848556267204489845927504400000000000)
      linear := (-178284638317055775512920233147086623020000000000)
      constant := (885030087346903790184578950450451425753873528712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108918494656271700083/50000000000000000000)
  centralHi := (217836989312543400167/100000000000000000000)
  directionLo := (223496035318074602413/100000000000000000000)
  directionHi := (111748017659037301207/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree021.table
  base := (-2298295792042407254928816624753964374557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-519364318934557627990537638224645449500000000000)
      constant := (2697782253142362702332599071906642154625496310907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree021.table
  base := (-575660934185677582412614075756642957797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-519954426381411081294307311990352699500000000000)
      constant := (2703960585850222986654825197008233286447773104588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223496035318074602413/100000000000000000000)
  centralHi := (111748017659037301207/50000000000000000000)
  directionLo := (229015287029147799967/100000000000000000000)
  directionHi := (7156727719660868749/3125000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree022.table
  base := (-1030171896436610880790908504980219919217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-1958599938690326149158450402371863006200000000000)
      constant := (10647699882922632712534423416904796329233723367103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree022.table
  base := (-5158493815371027403375286222280334863809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-9804127433878010150949051574298366031000000000000)
      constant := (53361411634368839502074008691999003414441656318831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229015287029147799967/100000000000000000000)
  centralHi := (7156727719660868749/3125000000000000000)
  directionLo := (23440461937254533349/10000000000000000000)
  directionHi := (234404619372545333491/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree023.table
  base := (-703101139266327841574387238773353348823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (407723927875640655349928631660090000000000000)
      linear := (-9676220837505882975193597859806249500000000000)
      constant := (54992801278598124042574885278594854410437120932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree023.table
  base := (-5631501243999097271646008116812933660059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (85932900)
      previous := (42966450)
      next := (42966450)
      square := (815447855751281310699857263320180000000000000)
      linear := (-19374433256882080980341345052495999000000000000)
      constant := (110240955341628972648496311630450990530835159589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23440461937254533349/10000000000000000000)
  centralHi := (234404619372545333491/100000000000000000000)
  directionLo := (23967279669026428239/10000000000000000000)
  directionHi := (239672796690264282391/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree024.table
  base := (-150662754181744222369967458764591487517/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4793021285471420148446938803293058000000000000)
      linear := (-118687595541231306996860011772118987900000000000)
      constant := (704311835687135000455751767618890564621703807468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree024.table
  base := (-1206473624664204256092728459851666485763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (9586042570942840296893877606586116000000000000)
      linear := (-237644954486738478361157588694275575800000000000)
      constant := (1411906412392343085323416027044364667272344525413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23967279669026428239/10000000000000000000)
  centralHi := (239672796690264282391/100000000000000000000)
  directionLo := (24482764011336150617/10000000000000000000)
  directionHi := (244827640113361506171/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree025.table
  base := (-3181344311591681123959984470684807881491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-5563162775670205535839987791653202925500000000000)
      constant := (34426243130627777031440856283443889729865290623869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree025.table
  base := (-6367809751458192904244385253837329370553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-11138970710915842213903611449714418351000000000000)
      constant := (69013328506098135552026906655618944120756660302327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/10000000000000000000)
  centralHi := (244827640113361506171/100000000000000000000)
  directionLo := (7808630119889197553/3125000000000000000)
  directionHi := (249876163836454321697/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree026.table
  base := (-1659739201348758114512006295083491195003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-5785383751985002256821275053561051395500000000000)
      constant := (37286547811338966423204226095049985773892844499754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree026.table
  base := (-1660857115119747819491823257812932672417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-5791959234964226450777565704093217895500000000000)
      constant := (37373769242348408462298053219713298809558156971806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7808630119889197553/3125000000000000000)
  centralHi := (249876163836454321697/100000000000000000000)
  directionLo := (127412343538378832637/50000000000000000000)
  directionHi := (10192987483070306611/4000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree027.table
  base := (-6860002023976964298246129114608705160031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-148335919217278987106236106554787651000000000000)
      constant := (994416821173678303254016534346265229140375263009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree027.table
  base := (-3431951148856628848581555871078493932473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-74252260672475701167942292386780575500000000000)
      constant := (498372172364902759946969032289793034413438395847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127412343538378832637/50000000000000000000)
  centralHi := (10192987483070306611/4000000000000000000)
  directionLo := (64919731704771569957/25000000000000000000)
  directionHi := (259678926819086279829/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree028.table
  base := (-1405948407632886884327931253669453765657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-2491930281845838279513539830950699334200000000000)
      constant := (17354941196736597369675006446388526231091208263063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree028.table
  base := (-3434150636817698610758607225307577129/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-6236906993976837138429085662565235335500000000000)
      constant := (43488905869425613338298990866216946728719741656064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64919731704771569957/25000000000000000000)
  centralHi := (259678926819086279829/100000000000000000000)
  directionLo := (264444075229635784077/100000000000000000000)
  directionHi := (132222037614817892039/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree029.table
  base := (-3575726802199204781149045774909434165539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-6452046680929392419765136839284596805500000000000)
      constant := (46626218232031000911960459072955486554321652897901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree029.table
  base := (-715441205880805193100586650637360155747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-1291876174696628496450969128360248811100000000000)
      constant := (9347061190301824822424838368980026009867983619373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264444075229635784077/100000000000000000000)
  centralHi := (132222037614817892039/50000000000000000000)
  directionLo := (134562432363384926821/50000000000000000000)
  directionHi := (269124864726769853643/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree030.table
  base := (-7227879019684765722619137141031373615263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-1483170590498708697943649800264987839000000000000)
      constant := (11108856372112015241158013497693185821979927879913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree030.table
  base := (-289218088059521708623552183873973525309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (1917208514188568059378775521317223200000000000)
      linear := (-59394264471017314009605383298108913560000000000)
      constant := (445393106739762669353282524905305428596054855259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134562432363384926821/50000000000000000000)
  centralHi := (269124864726769853643/100000000000000000000)
  directionLo := (8553925719755166339/3125000000000000000)
  directionHi := (273725623032165322849/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree031.table
  base := (-3630657289720060883392741424398471289117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-6896488633558985861727711363100293745500000000000)
      constant := (53477737388487640544711390377302871072949425701203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree031.table
  base := (-1815887714775452472990905281473065290703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-6904328632495753169906365600273261495500000000000)
      constant := (53602641056320555786914189741463305886860199652354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553925719755166339/3125000000000000000)
  centralHi := (273725623032165322849/100000000000000000000)
  directionLo := (69562580006464313129/25000000000000000000)
  directionHi := (278250320025857252517/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree032.table
  base := (-1813421029425353020782581152801758124231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-7118709609873782582708998625008142215500000000000)
      constant := (57089432100894438283244070087416921892448735543058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree032.table
  base := (-3627813072741789258616957543254320523231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-7126802512002058513732125579509270215500000000000)
      constant := (57222619622872903633740575469007808487519894412529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69562580006464313129/25000000000000000000)
  centralHi := (278250320025857252517/100000000000000000000)
  directionLo := (141351303924510084511/50000000000000000000)
  directionHi := (282702607849020169023/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree033.table
  base := (-3603300105855765948070181578158235180921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-815658954020953255965587320768443409500000000000)
      constant := (6758285698330935911613122704750302440949264977471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree033.table
  base := (-1441657104207259933571432171163095151691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (9586042570942840296893877606586116000000000000)
      linear := (-326634506289260615891461580388679063800000000000)
      constant := (2709613104184611250974099274321834601153516171741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141351303924510084511/50000000000000000000)
  centralHi := (282702607849020169023/100000000000000000000)
  directionLo := (71771463851755604353/25000000000000000000)
  directionHi := (287085855407022417413/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree034.table
  base := (-1780353791775116412654194547045537462339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-7563151562503376024671573148823839155500000000000)
      constant := (64682847571784469803698839887001735862131179458202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree034.table
  base := (-3561438365304005594562056828365863157969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-7571750271014669201383645537981287655500000000000)
      constant := (64833360387839602915108639541197925985334272658271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71771463851755604353/25000000000000000000)
  centralHi := (287085855407022417413/100000000000000000000)
  directionLo := (145701589099884807229/50000000000000000000)
  directionHi := (291403178199769614459/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree035.table
  base := (-699926352469190709099766402788010567429/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-1557074507763634549130572082146337525100000000000)
      constant := (13732800617733830116698571881141971074146854770411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree035.table
  base := (-1750132565647842411087146157573704308969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-7794224150520974545209405517217296375500000000000)
      constant := (68823559302374290034348329109170373662370900934542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145701589099884807229/50000000000000000000)
  centralHi := (291403178199769614459/100000000000000000000)
  directionLo := (295657464230266961113/100000000000000000000)
  directionHi := (147828732115133480557/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree036.table
  base := (-1710274381279912095667575548536796329243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-98859179199172462551038860156043655500000000000)
      constant := (898368165413070227224149812640003882152158551754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree036.table
  base := (-6842194766806673259225085770878478591521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-197943161235241478741609024603785311000000000000)
      constant := (1800905579425903383922383182270121842709330913119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295657464230266961113/100000000000000000000)
  centralHi := (147828732115133480557/50000000000000000000)
  directionLo := (59970279320749037207/20000000000000000000)
  directionHi := (74962849150936296509/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree037.table
  base := (-1661929179575707927575796369056058768483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-8229814491447766187615434934547384565500000000000)
      constant := (76994120769436695870337487958390485876611491874394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree037.table
  base := (-1662166654790987547563694610880566954333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-8239171909533585232860925475689313815500000000000)
      constant := (77172529370676138177716091431669547295922576134694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59970279320749037207/20000000000000000000)
  centralHi := (74962849150936296509/25000000000000000000)
  directionLo := (75996868329952169397/25000000000000000000)
  directionHi := (303987473319808677589/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree038.table
  base := (-6419792700413085728552440887117849151311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-16904070935525125817193444392910466071000000000000)
      constant := (162685497105633130703060207279611929114719473861249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree038.table
  base := (-6420614616349610979472747854960814527571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-16923291578079781153373370909850645071000000000000)
      constant := (163061935003341774241460242084576468242590741334589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75996868329952169397/25000000000000000000)
  centralHi := (303987473319808677589/100000000000000000000)
  directionLo := (308068024672321835387/100000000000000000000)
  directionHi := (77017006168080458847/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree039.table
  base := (-6157889792771221001894820160225323965637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-1927612543128302139906224324080684779000000000000)
      constant := (19069683662796203983651340711766696659149180195987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree039.table
  base := (-1539650153833692725496472868253357465857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-964902185394021768945827270462370139500000000000)
      constant := (9556873628205134287924834453488919581999053234414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308068024672321835387/100000000000000000000)
  centralHi := (77017006168080458847/25000000000000000000)
  directionLo := (156047614300612745377/50000000000000000000)
  directionHi := (62419045720245098151/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree040.table
  base := (-234499293537240583172170644531642833087/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17254876627697112534408979691855008800000000000)
      linear := (-711718193631372508044743737621674398040000000000)
      constant := (7232519739528598315402714979676399818523789948433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree040.table
  base := (-2931548396817465134375503865460723839241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-8906593548052501264338205413397339975500000000000)
      constant := (90615107504784481096000354066503799889648952606119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156047614300612745377/50000000000000000000)
  centralHi := (62419045720245098151/20000000000000000000)
  directionLo := (39508890535429668833/12500000000000000000)
  directionHi := (63214224856687470133/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree041.table
  base := (-2766984588839136856542639133484055751133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-9118698396706953071540583982178778445500000000000)
      constant := (95121418683976410329085346639280285730274919398547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree041.table
  base := (-276725004579303860725938059831985074753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-1825813485511761321632793078526669739100000000000)
      constant := (19068122366583249954951016161779661486964038860254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39508890535429668833/12500000000000000000)
  centralHi := (63214224856687470133/20000000000000000000)
  directionLo := (15999881210179421407/5000000000000000000)
  directionHi := (319997624203588428141/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree042.table
  base := (-5172685768963389694625682526871080483511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-2075759860671499953893749165352583759000000000000)
      constant := (22212948012220666583389882775516367463743205804561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree042.table
  base := (-2586572151548653668971210475884851672457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-1039060145229456883554413930207706379500000000000)
      constant := (11132033307709176526788259152606874558577468453807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15999881210179421407/5000000000000000000)
  centralHi := (319997624203588428141/100000000000000000000)
  directionLo := (161938262453693988853/50000000000000000000)
  directionHi := (323876524907387977707/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree043.table
  base := (-2389457171687852219251308376018132124183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-9563140349336546513503158505994475385500000000000)
      constant := (104916974708141586846590781441928770046834853853497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree043.table
  base := (-2389655101432954635164940110583910553153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-9574015186571417295815485351105366135500000000000)
      constant := (105158107496194858637492142497572013561254610815727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161938262453693988853/50000000000000000000)
  centralHi := (323876524907387977707/100000000000000000000)
  directionLo := (81927379152298198457/25000000000000000000)
  directionHi := (327709516609192793829/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree044.table
  base := (-1088223103946642626316063650351483322119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-9785361325651343234484445767902323855500000000000)
      constant := (109997490658068406036363150242982939086207436356242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree044.table
  base := (-4353234033018277264592398421869163094987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-19592978132155445279282490660682749711000000000000)
      constant := (220499962634569406069255193131002929261829647710533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81927379152298198457/25000000000000000000)
  centralHi := (327709516609192793829/100000000000000000000)
  directionLo := (165749095899778371993/50000000000000000000)
  directionHi := (331498191799556743987/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree045.table
  base := (-243426245117792335801472911226941645247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-123550398789705431548959667034693485500000000000)
      constant := (1422219363714652309380184083300517071344151609864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree045.table
  base := (-779022923642537765329639278602777591399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (112243220)
      previous := (56121610)
      next := (56121610)
      square := (1065115841215871144099319734065124000000000000)
      linear := (-49476360225106311029466692886801894200000000000)
      constant := (570191980450836565367862165411587321109876596761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165749095899778371993/50000000000000000000)
  centralHi := (331498191799556743987/100000000000000000000)
  directionLo := (335244052977111903619/100000000000000000000)
  directionHi := (16762202648855595181/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree046.table
  base := (-1702432602787044102136217631442427738079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (407723927875640655349928631660090000000000000)
      linear := (-19338002416410088235249565768843139500000000000)
      constant := (227833213333245018129216836278217699514264311009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree046.table
  base := (-851279833368834799081694683140507426937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (407723927875640655349928631660090000000000000)
      linear := (-19359993998280403265203715101726639500000000000)
      constant := (228354921786639679253307501319981553786635309454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335244052977111903619/100000000000000000000)
  centralHi := (16762202648855595181/5000000000000000000)
  directionLo := (169474259805630597649/50000000000000000000)
  directionHi := (338948519611261195299/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree047.table
  base := (-2883170044018206171315945451697354532761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-20904048509191466794856615107251738531000000000000)
      constant := (251938925220757838761581988335020128434633304971799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree047.table
  base := (-720847277962806357819349653741046789967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-10463910704596638671118525268049401015500000000000)
      constant := (126257582035771641427502153113809390109199865832706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169474259805630597649/50000000000000000000)
  centralHi := (338948519611261195299/100000000000000000000)
  directionLo := (342612934427190617139/100000000000000000000)
  directionHi := (17130646721359530857/5000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree048.table
  base := (-582463466671955069656751616607311601987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-1186027247878947790934399423948190859500000000000)
      constant := (14615202176304257090789442470983096079224658649674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree048.table
  base := (-2330042648030072679652633523266772023381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-2374752129800654225543174499396757719000000000000)
      constant := (29297185398843768933360823997282380457090410572931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342612934427190617139/100000000000000000000)
  centralHi := (17130646721359530857/5000000000000000000)
  directionLo := (34623856909211503977/10000000000000000000)
  directionHi := (346238569092115039771/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree049.table
  base := (-872508649517115835690125755949951648987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-10896466207225326839390882077441566205500000000000)
      constant := (137225817910952345212006391811404176676447226996533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree049.table
  base := (-1745179928378223674595662254046913330299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-21817716927218498717540090453042836911000000000000)
      constant := (275077975352110249933362721648196070731822582542741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34623856909211503977/10000000000000000000)
  centralHi := (346238569092115039771/100000000000000000000)
  directionLo := (2798613034968288403/800000000000000000)
  directionHi := (43728328671379506297/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree050.table
  base := (-564372569986553935306301491031945649149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-11118687183540123560372169339349414675500000000000)
      constant := (143036438308861735827698754020694172817271830219891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree050.table
  base := (-1128885196382627471219479541496533749633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-22262664686231109405191610411514854351000000000000)
      constant := (286725046063263302735166771274707300804065198960047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2798613034968288403/800000000000000000)
  centralHi := (43728328671379506297/12500000000000000000)
  directionLo := (353378259811275211277/100000000000000000000)
  directionHi := (176689129905637605639/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree051.table
  base := (-120277216124859518983554934817102601561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-1260100906650546697928161844584140349500000000000)
      constant := (16552073837192746871570266471276616166887374700222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree051.table
  base := (-12030736116498243927214961519337918291/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4793021285471420148446938803293058000000000000)
      linear := (-252306804947152445476034781888743019900000000000)
      constant := (3317953871676350335872173083207327020009258273364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353378259811275211277/100000000000000000000)
  centralHi := (176689129905637605639/50000000000000000000)
  directionLo := (71378909601475428429/20000000000000000000)
  directionHi := (178447274003688571073/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree052.table
  base := (39566254429208189565813936518379709909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-4625251654467886800933897545266044646200000000000)
      constant := (62008993157202305147101218465128224854082550871269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree052.table
  base := (24715936275429725892988724104385862493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-11576280102128165390247325164229444615500000000000)
      constant := (155375177657058918038423732916983490358324803068852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71378909601475428429/20000000000000000000)
  centralHi := (178447274003688571073/50000000000000000000)
  directionLo := (360376528491430654279/100000000000000000000)
  directionHi := (9009413212285766357/2500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree053.table
  base := (56751529048355892432169057365556941351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-11785350112484513723316031125072960085500000000000)
      constant := (161197881836035252296718465136641113031125031443128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree053.table
  base := (226983791534077990103448646188362924421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-11798753981634470734073085143465453335500000000000)
      constant := (161564271861395616202136925116138509961441600372522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360376528491430654279/100000000000000000000)
  centralHi := (9009413212285766357/2500000000000000000)
  directionLo := (363825186288250023109/100000000000000000000)
  directionHi := (36382518628825002311/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree054.table
  base := (329885573880889820036808894884959067279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (112243220)
      previous := (56121610)
      next := (56121610)
      square := (1065115841215871144099319734065124000000000000)
      linear := (-59296647352095360218752189565337326200000000000)
      constant := (827135069756578757635398408593930602563979579919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree054.table
  base := (329870210784176531731743114536884928121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (112243220)
      previous := (56121610)
      next := (56121610)
      square := (1065115841215871144099319734065124000000000000)
      linear := (-59364088203164326310611580852846726200000000000)
      constant := (829013319367272832923368987388964059455088479481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363825186288250023109/100000000000000000000)
  centralHi := (36382518628825002311/10000000000000000000)
  directionLo := (73448292034008451851/20000000000000000000)
  directionHi := (45905182521255282407/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree055.table
  base := (2422005350368697233534502757248010484733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-24459584130228214330557211297777314051000000000000)
      constant := (347826768097308352086107668772478522385870780679053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree055.table
  base := (2421939290576848672846935556331917897503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-24487403481294162843449210203874941551000000000000)
      constant := (348615890874206260249527492169229430887045035052623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73448292034008451851/20000000000000000000)
  centralHi := (45905182521255282407/12500000000000000000)
  directionLo := (370626245641036109331/100000000000000000000)
  directionHi := (92656561410259027333/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree056.table
  base := (3225726425676759577345474419052560151139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-24904026082857807772519785821593010991000000000000)
      constant := (360906944353095842288763824100860378913460488511699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree056.table
  base := (3225669630228309275666363812071896418069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-24932351240306773531100730162346958991000000000000)
      constant := (361725019564850784737925910480979628704155649505829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370626245641036109331/100000000000000000000)
  centralHi := (92656561410259027333/25000000000000000000)
  directionLo := (93495099419740491329/25000000000000000000)
  directionHi := (373980397678961965317/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree057.table
  base := (4060565379062629466791064507923276628107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-2816496448387489023831373371712078659000000000000)
      constant := (41581135592060781160407629861234379342260262483043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree057.table
  base := (4060516560948773564547987158715278258313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-2819699888813264913194694457868775159000000000000)
      constant := (41675307646482102327025470329497850920709069299537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93495099419740491329/25000000000000000000)
  centralHi := (373980397678961965317/100000000000000000000)
  directionLo := (377304733257163688391/100000000000000000000)
  directionHi := (47163091657145461049/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree058.table
  base := (4926500512183136554060826988827416404417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-25792909988116994656444934869224404871000000000000)
      constant := (387796586159919696826192806852161980741125974526097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree058.table
  base := (492645856115004477985682507973957822527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-2582224675833199490640377007929099387100000000000)
      constant := (38867412885127861605634272485959494452485707018607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377304733257163688391/100000000000000000000)
  centralHi := (47163091657145461049/12500000000000000000)
  directionLo := (380600033668422506013/100000000000000000000)
  directionHi := (190300016834211253007/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree059.table
  base := (5823513514709335850804946283567259648471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-26237351940746588098407509393040101811000000000000)
      constant := (401606033523612207255320492967060629720057835122311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree059.table
  base := (727934684165774521620704003759053018473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-13133597258672302797027645018881505655500000000000)
      constant := (201257045704769646954249336526749347884094889849572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380600033668422506013/100000000000000000000)
  centralHi := (190300016834211253007/50000000000000000000)
  directionLo := (383867046669220159099/100000000000000000000)
  directionHi := (3838670466692201591/1000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree060.table
  base := (3375794466805906516532629214143506679951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-1482321882965343418909449106491988819500000000000)
      constant := (23092141966383808435910512102667291824332144356999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree060.table
  base := (6751557976520368629190415994819835739433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-2968015808484135142411867777359447639000000000000)
      constant := (46288627725382572504424136815006406597469268402417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383867046669220159099/100000000000000000000)
  centralHi := (3838670466692201591/1000000000000000000)
  directionLo := (387106488461113436481/100000000000000000000)
  directionHi := (193553244230556718241/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree061.table
  base := (7710713725929951822760789844104549750917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-27126235846005774982332658440671495691000000000000)
      constant := (429954145844673944087242274719337801300307144232597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree061.table
  base := (7710687141862901450008147296901731717357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-27157090035369826969358329954707046191000000000000)
      constant := (430924797330719447158004219619072169841705732256637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387106488461113436481/100000000000000000000)
  centralHi := (193553244230556718241/50000000000000000000)
  directionLo := (195159522762046544111/50000000000000000000)
  directionHi := (390319045524093088223/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree062.table
  base := (2175219220455351672925937355603234601857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-13785338899317684212147616482243596315500000000000)
      constant := (222246399933999374966206124952117379095935566042274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree062.table
  base := (174017081160573753032393202551251076061/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8627438313848556267204489845927504400000000000)
      linear := (-552040755887648753140196998263581272620000000000)
      constant := (8909910597124860132809998155612065670852483803501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195159522762046544111/50000000000000000000)
  centralHi := (390319045524093088223/100000000000000000000)
  directionLo := (196752688157610666957/50000000000000000000)
  directionHi := (78701075263044266783/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree063.table
  base := (9722069106790766795612926820408386586911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-345865675941542739089602561583986291000000000000)
      constant := (5670055719009190024307897836833197991775985024671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree063.table
  base := (4861024757779138142477251016264883020543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-173129540453055853979391172047228895500000000000)
      constant := (2841418783447724252406071699252080056157453623423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196752688157610666957/50000000000000000000)
  centralHi := (78701075263044266783/20000000000000000000)
  directionLo := (99166528211113419029/25000000000000000000)
  directionHi := (396666112844453676117/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree064.table
  base := (10774282553761361484899052466187069105001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-28459561703894555308220382012118586511000000000000)
      constant := (474299282392747200139437664615596685906766712890041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree064.table
  base := (10774265740746749719706278806335716215709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-28491933312407659032312889830123098511000000000000)
      constant := (475367732983774445202980887061318551399682440609069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99166528211113419029/25000000000000000000)
  centralHi := (396666112844453676117/100000000000000000000)
  directionLo := (199900931069163457357/50000000000000000000)
  directionHi := (79960372427665382943/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree065.table
  base := (11857510597136185448931968238616376361359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-28904003656524148750182956535934283451000000000000)
      constant := (489567104315109888135296041235226153608999811830719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree065.table
  base := (11857496171281570673356470790642611607981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-28936881071420269719964409788595115951000000000000)
      constant := (490669197068843241764704013285903238954161118812221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199900931069163457357/50000000000000000000)
  centralHi := (79960372427665382943/20000000000000000000)
  directionLo := (201456603800557170179/50000000000000000000)
  directionHi := (402913207601114340359/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree066.table
  base := (1297174764223883464029956138607175728431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4793021285471420148446938803293058000000000000)
      linear := (-326093840101708246579394789552777559900000000000)
      constant := (5611977516261958371565438371369817456389223444519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree066.table
  base := (12971735267051190530153505502594386090373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-3264647647825875600846214416340792599000000000000)
      constant := (56246025850587320344765341347739715015918004434477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201456603800557170179/50000000000000000000)
  centralHi := (402913207601114340359/100000000000000000000)
  directionLo := (16240028411283697759/4000000000000000000)
  directionHi := (50750088785261555497/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree067.table
  base := (14116988964571451299383233893908251282801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-29792887561783335634108105583565677331000000000000)
      constant := (520831896690460243682149512656919040294130395179841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree067.table
  base := (2823395670117698854658581915602089819201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-5965355317889098219053489941107830166200000000000)
      constant := (104400567523359157792293457275868339654547169172241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16240028411283697759/4000000000000000000)
  centralHi := (50750088785261555497/12500000000000000000)
  directionLo := (409064910056715164909/100000000000000000000)
  directionHi := (40906491005671516491/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree068.table
  base := (7646615287103011549079200554065885793891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-15118664757206464538035340053690687135500000000000)
      constant := (268414431591000134893946328836094344259317257784531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree068.table
  base := (7646610736244562349946459042555772872317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-15135862174229050891459484832005584135500000000000)
      constant := (269017505079016408847895501802645396779948911209997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409064910056715164909/100000000000000000000)
  centralHi := (40906491005671516491/10000000000000000000)
  directionLo := (206053163364369008517/50000000000000000000)
  directionHi := (82421265345747603407/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree069.table
  base := (330009382027295768507603136815030941511/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19096200000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (1812106346113958468221905029600400000000000)
      linear := (-128887928868063526645802371901689020000000000)
      constant := (2323330705340666960030173899300918199326411791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree069.table
  base := (4125115324470288644675710358122971155949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (45302658652848961705547625740010000000000000)
      linear := (-3225863485346640671137417519689475500000000000)
      constant := (58213689221068481152666678491736740817882332938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206053163364369008517/50000000000000000000)
  centralHi := (82421265345747603407/20000000000000000000)
  directionLo := (415125461059663591271/100000000000000000000)
  directionHi := (51890682632457948909/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree070.table
  base := (17738701699867426796458933336103089758019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-31126213419672115959995829155012768151000000000000)
      constant := (569551929069665746143139941299722687532875747193779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree070.table
  base := (1108668438165117338021742800800864917299/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-15580809933241661579111004790477601575500000000000)
      constant := (285415026075786156242606092852280446750126620194072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415125461059663591271/100000000000000000000)
  centralHi := (51890682632457948909/12500000000000000000)
  directionLo := (104530698932820440833/25000000000000000000)
  directionHi := (418122795731281763333/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree071.table
  base := (9503962982822988669239990055614360282527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-15785327686150854700979201839414232545500000000000)
      constant := (293139013039553433075781721873902966363471307878607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree071.table
  base := (9503960116289221841369046407353424743619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-15803283812747966922936764769713610295500000000000)
      constant := (293796459621308314272859245396827839346568457603379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104530698932820440833/25000000000000000000)
  centralHi := (418122795731281763333/100000000000000000000)
  directionLo := (210549398123271820997/50000000000000000000)
  directionHi := (84219759249308728399/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree072.table
  base := (4061627973593760403701396780902556443267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (112243220)
      previous := (56121610)
      next := (56121610)
      square := (1065115841215871144099319734065124000000000000)
      linear := (-79049623024521735417088835068257190200000000000)
      constant := (1489499171633404703519145409280031890471201769987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree072.table
  base := (162465079641819339620575032773686945887/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (22448644)
      previous := (11224322)
      next := (11224322)
      square := (213023168243174228819863946813024800000000000)
      linear := (-15827908831856071374580271356987278040000000000)
      constant := (298567579813891156710714514724545158199580659035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210549398123271820997/50000000000000000000)
  centralHi := (84219759249308728399/20000000000000000000)
  directionLo := (424053911773530253533/100000000000000000000)
  directionHi := (212026955886765126767/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree073.table
  base := (10819670845692810372124066392558051522951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-16229769638780448142941776363229929485500000000000)
      constant := (310229671793556913277497662610499411129190792775991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree073.table
  base := (21639337482297262441361063906080813237619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-32496463143521155221176569456371255471000000000000)
      constant := (621849341022002446299447023746288700662936375857379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424053911773530253533/100000000000000000000)
  centralHi := (212026955886765126767/50000000000000000000)
  directionLo := (106747143984212138111/25000000000000000000)
  directionHi := (85397715187369710489/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree074.table
  base := (1437595624169861851891636067162790111507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-16451990615095244863923063625137777955500000000000)
      constant := (318957281323543348896900927843782738556610433334296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree074.table
  base := (1150076319054417805243627518617526286807/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-3294141090253376590882808941484327291100000000000)
      constant := (63934289428795137377151415842649211415213475708174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106747143984212138111/25000000000000000000)
  centralHi := (85397715187369710489/20000000000000000000)
  directionLo := (429903207560402816283/100000000000000000000)
  directionHi := (107475801890100704071/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree075.table
  base := (24394703529680885396825411056416902676129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-3705380353646675907756522419343472539000000000000)
      constant := (72845869014989570432154830211753982030957901242921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree075.table
  base := (24394700441486661686930693052346829373881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-3709595406838486288497734374812810039000000000000)
      constant := (73008889818986292860212964841203093808571744301569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429903207560402816283/100000000000000000000)
  centralHi := (107475801890100704071/25000000000000000000)
  directionLo := (432798211365143799713/100000000000000000000)
  directionHi := (216399105682571899857/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree076.table
  base := (25818861285948118330665163185681382372539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-33792865135449676611771276297906949791000000000000)
      constant := (673554118580382648732569193257746960064757318589099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree076.table
  base := (25818858641347459601908436784616681870391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-33831306420558987284131129331787307791000000000000)
      constant := (675060682806126532949888821298017498193335649421031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432798211365143799713/100000000000000000000)
  centralHi := (216399105682571899857/50000000000000000000)
  directionLo := (108918494656271700083/25000000000000000000)
  directionHi := (435673978625086800333/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree077.table
  base := (5454800476329938441625496803843225090917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-6847461417615854010746770164344529346200000000000)
      constant := (138347690917253621035667165125168809219426733172597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree077.table
  base := (340925001465888729998907986936338873659/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-3427625417957159797178264929025932523100000000000)
      constant := (69328491720121249944169518792714204083377362680152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108918494656271700083/25000000000000000000)
  centralHi := (435673978625086800333/100000000000000000000)
  directionLo := (43853088778460918429/10000000000000000000)
  directionHi := (438530887784609184291/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree078.table
  base := (28760126078460481500840138057258076045813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-3853527671189873721744047260615371519000000000000)
      constant := (78907314312992327307449792185795072458874113387037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree078.table
  base := (1150404965597162927653357437598590862333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (1917208514188568059378775521317223200000000000)
      linear := (-154316453060374260708596307772139300760000000000)
      constant := (3163345383220412030753884490762404192112874684517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43853088778460918429/10000000000000000000)
  centralHi := (438530887784609184291/100000000000000000000)
  directionLo := (44136930503978456339/10000000000000000000)
  directionHi := (441369305039784563391/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree079.table
  base := (7569307938140235850665048358007303759419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-17563095496669228468829499934677020305500000000000)
      constant := (364418120494396069027787182830853850383799880502358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree079.table
  base := (30277230093230498759639800924591683807843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-35166149697596819347085689207203360111000000000000)
      constant := (730464064596201455067791556201093830816047346276563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44136930503978456339/10000000000000000000)
  centralHi := (441369305039784563391/100000000000000000000)
  directionLo := (444189584886281746877/100000000000000000000)
  directionHi := (222094792443140873439/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree080.table
  base := (7956329719216981397340396270369480305663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-17785316472984025189810787196584868775500000000000)
      constant := (373874845431123782817098491257499394119797014774366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree080.table
  base := (636506349134602041874699904398773227371/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8627438313848556267204489845927504400000000000)
      linear := (-712221949132188600694744183313507551020000000000)
      constant := (14988379541589042162323858054630508209514148357211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444189584886281746877/100000000000000000000)
  centralHi := (222094792443140873439/50000000000000000000)
  directionLo := (223496035318074602413/50000000000000000000)
  directionHi := (446992070636149204827/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree081.table
  base := (835109675150656276817479831580826609319/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (56121610)
      previous := (28060805)
      next := (28060805)
      square := (532557920607935572049659867032562000000000000)
      linear := (-44463055430367461508128578909858561100000000000)
      constant := (946797750907216576681669525871473117128329313436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree081.table
  base := (33404385790772482896616031594597603008631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-445136360686691860770231223754906111000000000000)
      constant := (9489104302154122196233867994970408074298521561591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223496035318074602413/50000000000000000000)
  centralHi := (446992070636149204827/100000000000000000000)
  directionLo := (449777094905617779053/100000000000000000000)
  directionHi := (224888547452808889527/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree082.table
  base := (4376804470466427419305142878812533880421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-18229758425613618631773361720400565715500000000000)
      constant := (393152851467761662850983554342097808799880277529044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree082.table
  base := (35014434723946329851394239481516056879757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-36500992974634651410040249082619412431000000000000)
      constant := (788059478612458798221191170482167729370842667915037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449777094905617779053/100000000000000000000)
  centralHi := (224888547452808889527/50000000000000000000)
  directionLo := (5656812250948546667/1250000000000000000)
  directionHi := (452544980075883733361/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree083.table
  base := (3665546483202078128401698329130213889839/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-3690395880385683070550929796461682837100000000000)
      constant := (80594826481974019750306067701687092420501231298399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree083.table
  base := (1145483248202776503636882640034251313889/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-18472970366823631048845884520545714935500000000000)
      constant := (403872533675372468068776269314756918992856558951184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5656812250948546667/1250000000000000000)
  centralHi := (452544980075883733361/100000000000000000000)
  directionLo := (9105920774573583071/2000000000000000000)
  directionHi := (455296038728679153551/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree084.table
  base := (38327473942227078988683592245305476376527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-4149822306276269349719096943159169479000000000000)
      constant := (91759318196151547342221612905316298554460895303623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree084.table
  base := (19163736590668398198520323263527853613093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-2077271582925548488074627166642413739500000000000)
      constant := (45981900809380473735142169627202291210149986615757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9105920774573583071/2000000000000000000)
  centralHi := (455296038728679153551/100000000000000000000)
  directionLo := (229015287029147799967/50000000000000000000)
  directionHi := (91606114811659119987/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree085.table
  base := (10007615716833984601708692902728077798967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-18896421354558008794717223506124111125500000000000)
      constant := (422981249834598586446192017952714281089939206905294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree085.table
  base := (2501903888535493050248919092014585776113/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-18917918125836241736497404479017732375500000000000)
      constant := (423923460082488924997183697108825051211058759405064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229015287029147799967/50000000000000000000)
  centralHi := (91606114811659119987/20000000000000000000)
  directionLo := (230374440130799185359/50000000000000000000)
  directionHi := (460748880261598370719/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree086.table
  base := (41764431415529146908579306398582742138649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-38237284661745611031397021536063919191000000000000)
      constant := (866334172444042247887323420498056739207990183349609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree086.table
  base := (20882215429508133730510899263426682116617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-19140392005342547080323164458253741095500000000000)
      constant := (434131592026570467582266000869540355518476305726297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230374440130799185359/50000000000000000000)
  centralHi := (460748880261598370719/100000000000000000000)
  directionLo := (463451242907451500997/100000000000000000000)
  directionHi := (231725621453725750499/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree087.table
  base := (43529379424729510260263533956450856803451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-4297969623819467163706621784431068459000000000000)
      constant := (98549875779580142564326917345481398173220211308499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree087.table
  base := (8705875789775891729833918818376706263311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (9586042570942840296893877606586116000000000000)
      linear := (-860571817104393441073285530555099991800000000000)
      constant := (19753844581348754859457892059010343145394687525639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463451242907451500997/100000000000000000000)
  centralHi := (231725621453725750499/50000000000000000000)
  directionLo := (466137939286866584171/100000000000000000000)
  directionHi := (116534484821716646043/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree088.table
  base := (22662653378995872950131891342197354213971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-19563084283502398957661085291847656535500000000000)
      constant := (453903314161740500789604130479172062229449529807811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree088.table
  base := (45325306351162667161009614527730359552353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-39170679528710315535949368833451517071000000000000)
      constant := (909826386426270336013436793974934093102051130151473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137939286866584171/100000000000000000000)
  centralHi := (116534484821716646043/25000000000000000000)
  directionLo := (468809238745090666981/100000000000000000000)
  directionHi := (234404619372545333491/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree089.table
  base := (23576106649804031237328139667568831885209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-19785305259817195678642372553755505005500000000000)
      constant := (464453705656611186155739275536301705223609840558569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree089.table
  base := (23576106475915132678013307652215420446841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-19807813643861463111800444395961767255500000000000)
      constant := (465486662399015573355801300000854202986659454305481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468809238745090666981/100000000000000000000)
  centralHi := (234404619372545333491/50000000000000000000)
  directionLo := (471465402996758949579/100000000000000000000)
  directionHi := (23573270149837947479/5000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree090.table
  base := (49010098951817497856256382899408750097913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-494012993484740553077127402855885271000000000000)
      constant := (11731496678284008941962561101288156975358253519993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree090.table
  base := (49010098654554590271161503431846590616389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-494575000576981937175955663585130271000000000000)
      constant := (11757578039903546742624767425474611233840264306629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471465402996758949579/100000000000000000000)
  centralHi := (23573270149837947479/5000000000000000000)
  directionLo := (118526671606289006499/25000000000000000000)
  directionHi := (474106686425156025997/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree091.table
  base := (198824076687598940359800970552959987079/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-20229747212446789120604947077571201945500000000000)
      constant := (485919043584640865929035815214709172774151335710592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree091.table
  base := (50898963377969259942137943357818641046261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-40505522805748147598903928708867569391000000000000)
      constant := (973997875691750814255195259827831463046578839581701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118526671606289006499/25000000000000000000)
  centralHi := (474106686425156025997/100000000000000000000)
  directionLo := (476733336366554219301/100000000000000000000)
  directionHi := (238366668183277109651/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree092.table
  base := (52818807270453421164386549366005070757707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (85932900)
      previous := (42966450)
      next := (42966450)
      square := (815447855751281310699857263320180000000000000)
      linear := (-77323131148436997510723003173833839000000000000)
      constant := (1878389376117832323462684661956848489449149598603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree092.table
  base := (1650587720417145398018475088494512673253/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (407723927875640655349928631660090000000000000)
      linear := (-38705548737959128815269800252683919500000000000)
      constant := (941281179721625795360936565555590201295901235792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476733336366554219301/100000000000000000000)
  centralHi := (238366668183277109651/50000000000000000000)
  directionLo := (479345593380528564781/100000000000000000000)
  directionHi := (239672796690264282391/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree093.table
  base := (6846203726019335289892088333825678671179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-2297132129452931395840835733487433209500000000000)
      constant := (56430050516964608858182231054730543896679213881484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree093.table
  base := (54769629622647377419932040445977859998447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-4599490924863707663800774291756844919000000000000)
      constant := (113110739840776505700932916681092183746720698825703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479345593380528564781/100000000000000000000)
  centralHi := (239672796690264282391/50000000000000000000)
  directionLo := (481943691507084604067/100000000000000000000)
  directionHi := (120485922876771151017/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree094.table
  base := (56751431195335152221128601422922195929677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-41792820282782358567097617726589494711000000000000)
      constant := (1038056875163735123527738842582888077715502252161757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree094.table
  base := (2837571551842192401429277342518837434277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-4184036608278597966185848858428362171100000000000)
      constant := (104036138693399171403963462647048052503066289700714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481943691507084604067/100000000000000000000)
  centralHi := (120485922876771151017/25000000000000000000)
  directionLo := (30282991156961053863/6250000000000000000)
  directionHi := (484527858511376861809/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree095.table
  base := (58764211389936039043650867191658545958677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-42237262235411952009060192250405191651000000000000)
      constant := (1060615877522330493746180185564050623005125568350757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree095.table
  base := (29382105627270381286710940439415882432577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-21142656920899295174755004271377819575500000000000)
      constant := (531484836613835492731784022489455696541664195280657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30282991156961053863/6250000000000000000)
  centralHi := (484527858511376861809/100000000000000000000)
  directionLo := (48709831611674222429/10000000000000000000)
  directionHi := (487098316116742224291/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree096.table
  base := (60807970356435403584065708345816510813489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-4742411576449060605669196308246765399000000000000)
      constant := (120379768485000147545974842032618954840291871157561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree096.table
  base := (60807970240782617947819856696519854870161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-4747806844534577893017947611247517399000000000000)
      constant := (120646835270237346307477498502325622311051798651289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48709831611674222429/10000000000000000000)
  centralHi := (487098316116742224291/100000000000000000000)
  directionLo := (24482764011336150617/5000000000000000000)
  directionHi := (489655280226723012341/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree097.table
  base := (62882708064835450419280016376557207944401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-43126146140671138892985341298036585531000000000000)
      constant := (1106462991678111076968202627693140017101751054305441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree097.table
  base := (62882707966056585907941045303355376373187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-43175209359823811724813048459699674031000000000000)
      constant := (1108916919533971017713571700852158627458175643695667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/5000000000000000000)
  centralHi := (489655280226723012341/100000000000000000000)
  directionLo := (24609948056835448283/5000000000000000000)
  directionHi := (492198961136708965661/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree098.table
  base := (64988424489806663856132844325037298231491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-43570588093300732334947915821852282471000000000000)
      constant := (1129751103450145321979581621269874268996091563726131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree098.table
  base := (12997684881089660885271654392960410019671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-8724031423767284482492913683634338294200000000000)
      constant := (226451175904369998403732772524276426885768952341511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24609948056835448283/5000000000000000000)
  centralHi := (492198961136708965661/100000000000000000000)
  directionLo := (123682390933946323947/25000000000000000000)
  directionHi := (494729563735785295789/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree099.table
  base := (8390639951245560915301266612261070447679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-271697716332903245536484508306592465500000000000)
      constant := (7119026244885080021121998835921061998788866497276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree099.table
  base := (33562559768964277559558764618352093247319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-272006820233636006790840051707677215500000000000)
      constant := (7134804922137120194946335096373366063990967046359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123682390933946323947/25000000000000000000)
  centralHi := (494729563735785295789/100000000000000000000)
  directionLo := (497247287699335115979/100000000000000000000)
  directionHi := (24862364384966755799/5000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree100.table
  base := (69292793407258012847341596115900234128711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-44459471998559919218873064869483676351000000000000)
      constant := (1177056436333618328554769360887439337533309689212151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree100.table
  base := (8661599168218815926674887394302357636913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-22255026318430821893883804167557863175500000000000)
      constant := (589832236559497010894817242424451245451091036873732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497247287699335115979/100000000000000000000)
  centralHi := (24862364384966755799/5000000000000000000)
  directionLo := (499752327672908643393/100000000000000000000)
  directionHi := (249876163836454321697/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree101.table
  base := (71491445866453330435228400627509331452119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-44903913951189512660835639393299373291000000000000)
      constant := (1201073657429926309778613205692056477249544105151879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree101.table
  base := (2859657832557620820241901481300398304517/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17254876627697112534408979691855008800000000000)
      linear := (-1798200015834970179016765131743509751640000000000)
      constant := (48149364268535392890004972383157259640415190930197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499752327672908643393/100000000000000000000)
  centralHi := (249876163836454321697/50000000000000000000)
  directionLo := (502244873447838343133/100000000000000000000)
  directionHi := (251122436723919171567/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree102.table
  base := (73721076974696876345891171727640814945379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-5038706211535456233644245990790563359000000000000)
      constant := (136148212772718207699274421270590182855802058386171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree102.table
  base := (73721076929867595146210163113114772276551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-5044438683876318351452294250228862359000000000000)
      constant := (136449699795960448547284265009987157269449066630399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502244873447838343133/100000000000000000000)
  centralHi := (251122436723919171567/50000000000000000000)
  directionLo := (126181277532262104819/25000000000000000000)
  directionHi := (504725110129048419277/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree103.table
  base := (9497710840143298913643992915388462514229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (2142450)
      previous := (1071225)
      next := (1071225)
      square := (20330470152343661672175723079290000000000000)
      linear := (-2158205196363874990327117939529209500000000000)
      constant := (58904572009722984174968076035603583171088793684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree103.table
  base := (75981686682879934983570462383051674998797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4284900)
      previous := (2142450)
      next := (2142450)
      square := (40660940304687323344351446158580000000000000)
      linear := (-4321321134310441686372152720381919000000000000)
      constant := (118069945090482562865831238386418793222023452653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126181277532262104819/25000000000000000000)
  centralHi := (504725110129048419277/100000000000000000000)
  directionLo := (253596609147739275203/50000000000000000000)
  directionHi := (507193218295478550407/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree104.table
  base := (78273275096659019320055340482252184611523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-46237239809078292986723362964746464111000000000000)
      constant := (1274583539269285330999752008039953989037968752027443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree104.table
  base := (9784159382999696990120867320728304806917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-23144921836456043269186844084501898055500000000000)
      constant := (638702177306579541228486645832678850474051446114388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253596609147739275203/50000000000000000000)
  centralHi := (507193218295478550407/100000000000000000000)
  directionLo := (127412343538378832637/25000000000000000000)
  directionHi := (509649374153515330549/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree105.table
  base := (40297921046763849803662949230192214568239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-2593426764539327023815885416031231169500000000000)
      constant := (72198494780661639615700453045644680250681524790311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree105.table
  base := (80595842065652765851146041836711054950569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-5192754603547188580669467569719534839000000000000)
      constant := (144716468844988063229301527179659673577761962426481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127412343538378832637/25000000000000000000)
  centralHi := (509649374153515330549/100000000000000000000)
  directionLo := (512093749683800341883/100000000000000000000)
  directionHi := (128023437420950085471/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree106.table
  base := (82949387705258374849826312681044756879551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-47126123714337479870648512012377857991000000000000)
      constant := (1324805309247222723159455525900868184329925723396591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree106.table
  base := (82949387681470572149707807343628764417367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-47179739190937307913676728085947830991000000000000)
      constant := (1327735642437232020255389871273575188137448118807047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512093749683800341883/100000000000000000000)
  centralHi := (128023437420950085471/25000000000000000000)
  directionLo := (514526512781760999561/100000000000000000000)
  directionHi := (257263256390880499781/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree107.table
  base := (85333911926381696760744567320636673557129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-47570565666967073312611086536193554931000000000000)
      constant := (1350280748852738677315090401305283547369571102307289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree107.table
  base := (21333477976520874754628811791278556975749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-23812343474974959300664124022209924215500000000000)
      constant := (676633311553868726367269120628688126436483390341418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514526512781760999561/100000000000000000000)
  centralHi := (257263256390880499781/50000000000000000000)
  directionLo := (1033895654784378263/200000000000000000)
  directionHi := (516947827392189131501/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree108.table
  base := (87749414752293888728134013513186253746177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-592777871846872429068810630370484591000000000000)
      constant := (16987644751436599599624891019386407077010398458497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree108.table
  base := (43874707367487421943494094848149378645687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-296726140178781044993702271622789295500000000000)
      constant := (8512599763051578031345227542379962889009557399607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1033895654784378263/200000000000000000)
  centralHi := (516947827392189131501/100000000000000000000)
  directionLo := (64919731704771569957/12500000000000000000)
  directionHi := (519357853638172559657/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree109.table
  base := (90195896179122252133761293803829292489181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-48459449572226260196536235583824948811000000000000)
      constant := (1401960737286339923062882585549727361674695336941421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree109.table
  base := (11274487020543292395521670792037223615749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-24257291233987569988315643980681941655500000000000)
      constant := (702529628977679974828496635131045635785565709642836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64919731704771569957/12500000000000000000)
  centralHi := (519357853638172559657/100000000000000000000)
  directionLo := (52175674794466661767/10000000000000000000)
  directionHi := (521756747944666617671/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree110.table
  base := (3706934248144460071465485664352349394509/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17254876627697112534408979691855008800000000000)
      linear := (-1956155660994234145539952404305625830040000000000)
      constant := (57126611444447397593715083666521263277349198939869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree110.table
  base := (46336678095503157992678952487478772612941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-24479765113493875332141403959917950375500000000000)
      constant := (715660456064649746775006771012783046014883461615581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52175674794466661767/10000000000000000000)
  centralHi := (521756747944666617671/100000000000000000000)
  directionLo := (2047440090456935417/390625000000000000)
  directionHi := (524144663156975466753/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree111.table
  base := (95181794823027706468521944515856285426597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-5483148164165049675606820514606260299000000000000)
      constant := (161623652371072979297185006305995171336584144415053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree111.table
  base := (95181794812275209885847601681586363779799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-5489386442888929039103814208700879799000000000000)
      constant := (161980680459439575870549168823298068764431204820751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2047440090456935417/390625000000000000)
  centralHi := (524144663156975466753/100000000000000000000)
  directionLo := (52652174865439716019/10000000000000000000)
  directionHi := (526521748654397160191/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree112.table
  base := (12215151504384638709753052702662420193171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-24896387715057520261211979577636019815500000000000)
      constant := (740651746485356418582508754417931861966687467820044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree112.table
  base := (24430303006476430294253755513067066954489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-24924712872506486019792923918389967815500000000000)
      constant := (742287446985654214345343106456105948630512254398098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52652174865439716019/10000000000000000000)
  centralHi := (526521748654397160191/100000000000000000000)
  directionLo := (105777630091854313631/20000000000000000000)
  directionHi := (132222037614817892039/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree113.table
  base := (50145803918918763727680404308775703779167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-25118608691372316982193266839543868285500000000000)
      constant := (754118575501739607119883301529927278315006485640847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree113.table
  base := (100291607830015359230244049150693228762291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-50294373504025582727237367795251953071000000000000)
      constant := (1511567221637500479037653049242400638443328433488931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105777630091854313631/20000000000000000000)
  centralHi := (132222037614817892039/25000000000000000000)
  directionLo := (531244011341656427309/100000000000000000000)
  directionHi := (53124401134165642731/10000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree114.table
  base := (10289298222970037664958109424438229844897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4793021285471420148446938803293058000000000000)
      linear := (-563129548170824748959434535587815927900000000000)
      constant := (17060153838191385634014286881869409634101102931753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree114.table
  base := (51446491111514725873823943465049386951971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-2818851181279899634160493764095776139500000000000)
      constant := (85489061507378695078041477500331815880731844673979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531244011341656427309/100000000000000000000)
  centralHi := (53124401134165642731/10000000000000000000)
  directionLo := (133397367729960962411/25000000000000000000)
  directionHi := (106717894183968769929/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree115.table
  base := (26381333802330422068596691279578107118339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (407723927875640655349928631660090000000000000)
      linear := (-48323347153122704015417469495953809500000000000)
      constant := (1477158389670452143131224876764057211673790269062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree115.table
  base := (105525335203632997428347003983998809684399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (85932900)
      previous := (42966450)
      next := (42966450)
      square := (815447855751281310699857263320180000000000000)
      linear := (-96756652215596983180605685656325119000000000000)
      constant := (2960836579313154529058017911308978773127284908271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133397367729960962411/25000000000000000000)
  centralHi := (106717894183968769929/20000000000000000000)
  directionLo := (66990583219614692977/12500000000000000000)
  directionHi := (535924665756917543817/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree116.table
  base := (108188666775580715238476856066031983203209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-51570543240633414290274257250534827391000000000000)
      constant := (1590496343505310720491967223807582931177742074596569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree116.table
  base := (54094333385364995842496214549481736211689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-25814608390531707395095963835334002695500000000000)
      constant := (797002775804264477574105734655733529752541828744249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66990583219614692977/12500000000000000000)
  centralHi := (535924665756917543817/100000000000000000000)
  directionLo := (107649945890707941457/20000000000000000000)
  directionHi := (269124864726769853643/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree117.table
  base := (110882976927544958956843235799049397599901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-642160311027938367064652244127784251000000000000)
      constant := (19980273421465652670755325538206984565783657996061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree117.table
  base := (110882976923409067373444855577976217339849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5325579206079355720496598670325620000000000000)
      linear := (-642890920247852166393128983075802751000000000000)
      constant := (20024347044296454881033604420351230997882224303689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107649945890707941457/20000000000000000000)
  centralHi := (269124864726769853643/50000000000000000000)
  directionLo := (540564792737145981419/100000000000000000000)
  directionHi := (27028239636857299071/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree118.table
  base := (113608265664440621255787582010726437314941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-52459427145892601174199406298166221271000000000000)
      constant := (1646550987171208047875961977010526629569596384397581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree118.table
  base := (11360826566091447190641679996210496227139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-5251911229908863616549496758761204027100000000000)
      constant := (165018222739476686269734500454643226256844327627699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540564792737145981419/100000000000000000000)
  centralHi := (27028239636857299071/5000000000000000000)
  directionLo := (33929373971732310717/6250000000000000000)
  directionHi := (542869983547716971473/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree119.table
  base := (23272906597125528347128820911202357709633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86274383138485562672044898459275044000000000000)
      linear := (-10580773819704438923232396164396383642200000000000)
      constant := (334988572720498060648656899891096004594030183399953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree119.table
  base := (4654581319304862149202850323887089813637/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17254876627697112534408979691855008800000000000)
      linear := (-2118562402324049874125859501843362308440000000000)
      constant := (67145436081140281995874756022586922232862858004117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33929373971732310717/6250000000000000000)
  centralHi := (542869983547716971473/100000000000000000000)
  directionLo := (136291356780071392617/25000000000000000000)
  directionHi := (545165427120285570469/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree120.table
  base := (59575889445289305355416711220063375914719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-2963795058397321558784697519210978619500000000000)
      constant := (94643209801795826659978113106186657452532327679831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree120.table
  base := (23830355777603211852081210343086360345351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (9586042570942840296893877606586116000000000000)
      linear := (-1186866840380307945351066833434579447800000000000)
      constant := (37940736321977769666127235976694056156459128721599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136291356780071392617/25000000000000000000)
  centralHi := (545165427120285570469/100000000000000000000)
  directionLo := (8553925719755166339/1562500000000000000)
  directionHi := (547451246064330645697/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree121.table
  base := (3049250084471523942276841325203653590603/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43137191569242781336022449229637522000000000000)
      linear := (-5379275300378138150008712986961331209100000000000)
      constant := (173245572566051513771086640664991970968686247878892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree121.table
  base := (121970003376676649644693162537138758977921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-53853955576126468228449527463028092591000000000000)
      constant := (1736273924776053083594272900554570922688667335879761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553925719755166339/1562500000000000000)
  centralHi := (547451246064330645697/100000000000000000000)
  directionLo := (137431890110049876933/25000000000000000000)
  directionHi := (549727560440199507733/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree122.table
  base := (124819206450121908213756423874634755640669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-54237194956410974942049704393429009031000000000000)
      constant := (1761576711286900710743517031743383317629938498632429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree122.table
  base := (62409603224130069104296217343229703203649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-27149451667569539458050523710750055015500000000000)
      constant := (882729136444755694112042585983961855779248612014609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137431890110049876933/25000000000000000000)
  centralHi := (549727560440199507733/100000000000000000000)
  directionLo := (551994487832693946453/100000000000000000000)
  directionHi := (275997243916346973227/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree123.table
  base := (12769938810407578031684725962962418171957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4793021285471420148446938803293058000000000000)
      linear := (-607573743433784093155691987969385621900000000000)
      constant := (19899341481237241469234816763823296425023135321693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree123.table
  base := (63849694051244513385554295078776687020679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-3041325060786204977986253743331784859500000000000)
      constant := (99715898823847133463509848295455530601459947895871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551994487832693946453/100000000000000000000)
  centralHi := (275997243916346973227/50000000000000000000)
  directionLo := (2165047435241982233/390625000000000000)
  directionHi := (554252143421947451649/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree124.table
  base := (130610548340493258277893258635583936169257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-55126078861670161825974853441060402911000000000000)
      constant := (1820547791733763958676622640740594028576443076284537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree124.table
  base := (130610548339140984353601603665450096631229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-55188798853164300291404087338444144911000000000000)
      constant := (1824557642595163057614508546586989059404561196845389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2165047435241982233/390625000000000000)
  centralHi := (554252143421947451649/100000000000000000000)
  directionLo := (556500640051714505033/100000000000000000000)
  directionHi := (278250320025857252517/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree125.table
  base := (66776343579596168658589647389175033668803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-27785260407149877633968713982438049925500000000000)
      constant := (925198943277027326714867715579973988980259192175923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree125.table
  base := (133552687158039967031410298371178122908331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-55633746612176910979055607296916162351000000000000)
      constant := (1854472664187175327103369101789840149720586686876571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556500640051714505033/100000000000000000000)
  centralHi := (278250320025857252517/50000000000000000000)
  directionLo := (34921255518449156627/6250000000000000000)
  directionHi := (558740088295186506033/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree126.table
  base := (5461032182401227214405818816900885915423/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (22448644)
      previous := (11224322)
      next := (11224322)
      square := (213023168243174228819863946813024800000000000)
      linear := (-27661710008360172202419754315403356440000000000)
      constant := (928637539640572401079307283396846528439986259103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree126.table
  base := (68262902279524362172731796374796094233243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2662789603039677860248299335162810000000000000)
      linear := (-346164780069071121399426711453013455500000000000)
      constant := (11633526195093968017309844682158829131008131268123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34921255518449156627/6250000000000000000)
  centralHi := (558740088295186506033/100000000000000000000)
  directionLo := (22438823860737717919/4000000000000000000)
  directionHi := (70121324564805368497/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree127.table
  base := (34882475135724792004584187436316170955359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-28229702359779471075931288506253746865500000000000)
      constant := (955413592694013865451266683255206306597659760369438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree127.table
  base := (139529900542062477131642848433631369571739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-56523642130202132354358647213860197231000000000000)
      constant := (1915033380849257901676368939795705004847655125756299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22438823860737717919/4000000000000000000)
  centralHi := (70121324564805368497/12500000000000000000)
  directionLo := (563192270941640868863/100000000000000000000)
  directionHi := (549992452091446161/97656250000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree128.table
  base := (142564975107716456814059849478340678076169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431371915692427813360224492296375220000000000000)
      linear := (-56903846672188535593825151536323190671000000000000)
      constant := (1941406389401623532052401500295427027963223085987929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree128.table
  base := (17820621888375448119671911734611788651709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215685957846213906680112246148187610000000000000)
      linear := (-28484294944607371521005083586166107335500000000000)
      constant := (972839537959622640770333527279429856157281881940276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell086.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563192270941640868863/100000000000000000000)
  centralHi := (549992452091446161/97656250000000000)
  directionLo := (141351303924510084511/25000000000000000000)
  directionHi := (113081043139608067609/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree129.table
  base := (72815514127212194650301739995607468592383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23965106427357100742234694016465290000000000000)
      linear := (-3186016034712118279765984781118827089500000000000)
      constant := (109568257211828893229439107962322097145636070926967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree129.table
  base := (145631028253817049524219819210791190141869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47930212854714201484469388032930580000000000000)
      linear := (-6379281960914150414406854125644914679000000000000)
      constant := (219618703201684439665926377848166226104120035020181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell086.Kernel129
