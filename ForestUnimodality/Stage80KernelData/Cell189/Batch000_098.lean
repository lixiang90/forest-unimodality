import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell189.Parameters
import ForestUnimodality.BinomialMassData.Q859_1584.Batch000_049
import ForestUnimodality.BinomialMassData.Q859_1584.Batch050_099
import ForestUnimodality.BinomialMassData.Q1291_2376.Batch000_049
import ForestUnimodality.BinomialMassData.Q1291_2376.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree000.table
  base := (401985499096052519576893763/12500000000000000000000000)
  polynomial :=
    { denominator := 220000000000000000000000000000000000000000
      center := (859)
      previous := (0)
      next := (725)
      square := (37772484896296463219300675600000000000000)
      linear := (-137284931013178737035929088000000000000000)
      constant := (7074944784090524344553330228800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree000.table
  base := (401985499096052519576893763/12500000000000000000000000)
  polynomial :=
    { denominator := 330000000000000000000000000000000000000000
      center := (1291)
      previous := (0)
      next := (1085)
      square := (56658727344444694828951013400000000000000)
      linear := (-205927396519768105553893632000000000000000)
      constant := (10612417176135786516829995343200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree001.table
  base := (98206841064955781840459001749924580621379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-158823258624400749342564507790950000000000000)
      constant := (3926332944560963920917204111910197946180542316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree001.table
  base := (1226089669260920775389225205466492022077/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-715023369151115873449953134509650000000000000)
      constant := (17648138916995330499728204828658816539062414880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9962344360721768631/20000000000000000000)
  directionHi := (12452930450902210789/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree002.table
  base := (61876038418786351359888387354235554206221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-195325643716059243986116198173900000000000000)
      constant := (2598047274763989315285365994644069417100688084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree002.table
  base := (123477084255974735276834704369099065257123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-879602807404891600754348590683300000000000000)
      constant := (11668806261140402185502232889421096947265562707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9962344360721768631/20000000000000000000)
  centralHi := (12452930450902210789/25000000000000000000)
  directionLo := (70444412539819233311/100000000000000000000)
  directionHi := (2201387891869351041/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree003.table
  base := (10049154829721730347282796040251528878499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-25758669867524193181074209839650000000000000)
      constant := (207105512800888678547206188039497326678966576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree003.table
  base := (80150896431041962005445386886082880838027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-116020249517629703117638227428550000000000000)
      constant := (929965669501857592931710972506307690093502627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70444412539819233311/100000000000000000000)
  centralHi := (2201387891869351041/3125000000000000000)
  directionLo := (43138216488168474893/50000000000000000000)
  directionHi := (86276432976336949787/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree004.table
  base := (53616669044595809814858249062895294391779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-268330413899376233273219578939800000000000000)
      constant := (1474692754572002646273866080533348560667651958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree004.table
  base := (26710787508133465002952840695512610024703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-1208761683912443055363139503030600000000000000)
      constant := (6623993044548803865547271001625893635338053854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43138216488168474893/50000000000000000000)
  centralHi := (86276432976336949787/100000000000000000000)
  directionLo := (99623443607217686311/100000000000000000000)
  directionHi := (12452930450902210789/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree005.table
  base := (18201105078163758777692548328286679754779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-304832798991034727916771269322750000000000000)
      constant := (1292667557666662220185934123156018180606355916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree005.table
  base := (18125126994997485594908903100905132968519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-1373341122166218782667534959204250000000000000)
      constant := (5810820985332522155578369712230716123040184942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99623443607217686311/100000000000000000000)
  centralHi := (12452930450902210789/12500000000000000000)
  directionLo := (27845599007294450633/25000000000000000000)
  directionHi := (111382396029177802533/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree006.table
  base := (6209577161935144673081544988450833731119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-37926131564743691395591439967300000000000000)
      constant := (137911084023427775628790761804002413465508728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree006.table
  base := (12360367601415355943830632157310806428147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-170880062268888278885770046153100000000000000)
      constant := (620525658367539632273773484906843927604537494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27845599007294450633/25000000000000000000)
  centralHi := (111382396029177802533/100000000000000000000)
  directionLo := (762583135176931559/625000000000000000)
  directionHi := (122013301628309049441/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree007.table
  base := (668659803091846361544179928573394408297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-377837569174351717203874650088650000000000000)
      constant := (1276998932211521699958330911262971617285944850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree007.table
  base := (8312466182146659921146356775750568347867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-1702499998673770237276325871551550000000000000)
      constant := (5750949780877783737633688887243023141794000406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (762583135176931559/625000000000000000)
  centralHi := (122013301628309049441/100000000000000000000)
  directionLo := (32947357067070687459/25000000000000000000)
  directionHi := (131789428268282749837/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree008.table
  base := (10768034135697707807313130317021913853697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-414339954266010211847426340471600000000000000)
      constant := (1375195336135846389558626820420163555360168594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree008.table
  base := (2139170357693011633877974252702593795133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-1867079436927545964580721327725200000000000000)
      constant := (6197717306001185644258368051295015480374433985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32947357067070687459/25000000000000000000)
  centralHi := (131789428268282749837/100000000000000000000)
  directionLo := (70444412539819233311/50000000000000000000)
  directionHi := (140888825079638466623/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree009.table
  base := (6247730521965547555085508417400359278833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-5565954806884798845567630010550000000000000)
      constant := (18780020366592844595248557047165574445477586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree009.table
  base := (6190058909167463520662280045772226154503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-25082208335571872739322429430850000000000000)
      constant := (84684640506543535022822788877655329282253767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70444412539819233311/50000000000000000000)
  centralHi := (140888825079638466623/100000000000000000000)
  directionLo := (149435165410826529467/100000000000000000000)
  directionHi := (37358791352706632367/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree010.table
  base := (2705896336099539287166909493307131877403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-487344724449327201134529721237500000000000000)
      constant := (1706143090670241043352667731783275149060853606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree010.table
  base := (1329631024400223910836989648401479410537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-2196238313435097419189512240072500000000000000)
      constant := (7696622145374879646446600781932629694648116466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149435165410826529467/100000000000000000000)
  centralHi := (37358791352706632367/25000000000000000000)
  directionLo := (157518495074074416533/100000000000000000000)
  directionHi := (78759247537037208267/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree011.table
  base := (-34363348643058914501826271511355447239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-47622464503725972343461946510950000000000000)
      constant := (174962853966381212124294600624368620872080408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree011.table
  base := (-175520461901242811320697741379149120639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-214619795608079376953991608749650000000000000)
      constant := (789509764088320617565537380069783728201595859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157518495074074416533/100000000000000000000)
  centralHi := (78759247537037208267/50000000000000000000)
  directionLo := (165206791384135679087/100000000000000000000)
  directionHi := (10325424461508479943/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree012.table
  base := (-2462673553609336620314144017813098494159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-62261054959182687824625900222600000000000000)
      constant := (241443471349593644453175846843678071479721698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree012.table
  base := (-2493954953938992928318704355793153495663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-280599687771405430422033683602200000000000000)
      constant := (1089729274714296294155655093677821302589006937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165206791384135679087/100000000000000000000)
  centralHi := (10325424461508479943/6250000000000000000)
  directionLo := (43138216488168474893/25000000000000000000)
  directionHi := (172552865952673899573/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree013.table
  base := (-4390029870733432705901293964374842442829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-596851879724302685065184792386350000000000000)
      constant := (2448985187384685285667986822002466525935665942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree013.table
  base := (-4415842585255629511946516707634502768471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-2689976628196424601102698608593450000000000000)
      constant := (11054922807405320383676055933228052520295941561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43138216488168474893/25000000000000000000)
  centralHi := (172552865952673899573/100000000000000000000)
  directionLo := (17959871708205926963/10000000000000000000)
  directionHi := (179598717082059269631/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree014.table
  base := (-6002398116054891668799709839981234256107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-633354264815961179708736482769300000000000000)
      constant := (2750948698499517361420938429867006596111790586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree014.table
  base := (-752968063736202401263246755702419658279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-2854556066450200328407094064767100000000000000)
      constant := (12419402773064908897501618112860599614902941512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17959871708205926963/10000000000000000000)
  centralHi := (179598717082059269631/100000000000000000000)
  directionLo := (4659459920860040561/2500000000000000000)
  directionHi := (186378396834401622441/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree015.table
  base := (-294343376779207581248908385156501883699/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-74428516656402186039143130350250000000000000)
      constant := (341969895303601364927779109562095659932589450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree015.table
  base := (-1475249889879950442018225888660998840103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-335459500522664006190165502326750000000000000)
      constant := (1543981701874161429471840139381402126840752485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4659459920860040561/2500000000000000000)
  centralHi := (186378396834401622441/100000000000000000000)
  directionLo := (96459984495646962211/50000000000000000000)
  directionHi := (192919968991293924423/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree016.table
  base := (-2125338678373832898634553780528161631677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-706359034999278168995839863535200000000000000)
      constant := (3428487967274779378537793487631947902783469784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree016.table
  base := (-4257984081757268642203316332663235148737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-3183714942957751783015884977114400000000000000)
      constant := (15480461786308060256597022706855417381530115934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96459984495646962211/50000000000000000000)
  centralHi := (192919968991293924423/100000000000000000000)
  directionLo := (199246887214435372623/100000000000000000000)
  directionHi := (12452930450902210789/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree017.table
  base := (-2365606986763695357146182363192735179867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-742861420090936663639391553918150000000000000)
      constant := (3802603672289213249088308596169488707516988264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree017.table
  base := (-1894900894934814831583627456631959285079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-3348294381211527510320280433288050000000000000)
      constant := (17170494439813112314922328034242666892112332445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199246887214435372623/100000000000000000000)
  centralHi := (12452930450902210789/6250000000000000000)
  directionLo := (25672373798770187749/12500000000000000000)
  directionHi := (205378990390161501993/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree018.table
  base := (-10265688387234006019132969074754237106661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-9621775372624631583740040053100000000000000)
      constant := (51847012263858032001808391700528224620188038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree018.table
  base := (-41102615465948927733838363307385242209/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-43368812585991397995366369005700000000000000)
      constant := (234121411130480917352229599492801867808599750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25672373798770187749/12500000000000000000)
  centralHi := (205378990390161501993/100000000000000000000)
  directionLo := (105666618809728849967/50000000000000000000)
  directionHi := (42266647523891539987/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree019.table
  base := (-437172998866451428874707254747250333707/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-815866190274253652926494934684050000000000000)
      constant := (4619144390969251856180174464196952161466884650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree019.table
  base := (-10937534485784727857039471864594852058843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-3677453257719078964929071345635350000000000000)
      constant := (20858883187961795490868669394855137069741517813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105666618809728849967/50000000000000000000)
  centralHi := (42266647523891539987/20000000000000000000)
  directionLo := (54281065386423130147/25000000000000000000)
  directionHi := (217124261545692520589/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree020.table
  base := (-1433412979807948070937620768095981560779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-852368575365912147570046625067000000000000000)
      constant := (5060939100839902292259374225052135555564880336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree020.table
  base := (-11474054578508966642358347793772805072767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-3842032695972854692233466801809000000000000000)
      constant := (22854414266525302293545730192502844637336295697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54281065386423130147/25000000000000000000)
  centralHi := (217124261545692520589/100000000000000000000)
  directionLo := (44552958411671121013/20000000000000000000)
  directionHi := (111382396029177802533/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree021.table
  base := (-297260303545618954279375261916548603333/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-98763440050841182468177590605550000000000000)
      constant := (613864519243126662512895762143409973177629040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree021.table
  base := (-11895953140217587610183967216185279841493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-445179126025181157726429139775850000000000000)
      constant := (2772164473466703434079575290604827447273527107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44552958411671121013/20000000000000000000)
  centralHi := (111382396029177802533/50000000000000000000)
  directionLo := (114132992830559881313/50000000000000000000)
  directionHi := (228265985661119762627/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree022.table
  base := (-3051754132364111910875984555753127161081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-84124849595384466987013636893900000000000000)
      constant := (546409554998683752563634482821397959595814632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree022.table
  base := (-6105778175316038037081344054382645300399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-379199233861855104258387064923300000000000000)
      constant := (2467576975272711712031689097535423634672200838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114132992830559881313/50000000000000000000)
  centralHi := (228265985661119762627/100000000000000000000)
  directionLo := (116818842485793632453/50000000000000000000)
  directionHi := (233637684971587264907/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree023.table
  base := (-12423625334291904954696810745171704462083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-961875730640887631500701696215850000000000000)
      constant := (6517984819889888633891088559480973936634249034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree023.table
  base := (-621366918499553836626783112511897513831/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-4335771010734181874146653170329950000000000000)
      constant := (29435442587723305460255783807591920019049626420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116818842485793632453/50000000000000000000)
  centralHi := (233637684971587264907/100000000000000000000)
  directionLo := (238888625656230803977/100000000000000000000)
  directionHi := (119444312828115401989/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree024.table
  base := (-12545311697366440345328792860383124525553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-110930901748060680682694820733200000000000000)
      constant := (783013374910074208705959469319985554783345566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree024.table
  base := (-6274171721494452793419365614873001594541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-500038938776439733494560958500400000000000000)
      constant := (3536146988065613318917590418757059422743807318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238888625656230803977/100000000000000000000)
  centralHi := (119444312828115401989/50000000000000000000)
  directionLo := (244026603256618098881/100000000000000000000)
  directionHi := (122013301628309049441/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree025.table
  base := (-12576035679531989837481508048438198466801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1034880500824204620787805076981750000000000000)
      constant := (7597834142775039361682775320781194121153766798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree025.table
  base := (-786156701057827750058644921252200903663/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-4664929887241733328755444082677250000000000000)
      constant := (34312640483088814468930876589041093142820646928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244026603256618098881/100000000000000000000)
  centralHi := (122013301628309049441/50000000000000000000)
  directionLo := (249058609018044215779/100000000000000000000)
  directionHi := (12452930450902210789/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree026.table
  base := (-625944576341415235608763373110039199493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1071382885915863115431356767364700000000000000)
      constant := (8170065472232131879267948710966508982230764280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree026.table
  base := (-12520903356614048682880357127654641685367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-4829509325495509056059839538850900000000000000)
      constant := (36897124234318614949013448621917849211575462297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249058609018044215779/100000000000000000000)
  centralHi := (12452930450902210789/5000000000000000000)
  directionLo := (253990941482256678113/100000000000000000000)
  directionHi := (126995470741128339057/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree027.table
  base := (-6188149308985113177129857374000124735037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-13677595938364464321912450095650000000000000)
      constant := (108194653554325643336831267650376127128242092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree027.table
  base := (-12377933940311716764822219145361388342603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (14201)
      previous := (0)
      next := (11935)
      square := (623246000788891643118461147400000000000000)
      linear := (-20551805612136974417136769526850000000000000)
      constant := (162874741816292192493315062445661941031635111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253990941482256678113/100000000000000000000)
  centralHi := (126995470741128339057/50000000000000000000)
  directionLo := (129414649464505424679/50000000000000000000)
  directionHi := (258829298929010849359/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree028.table
  base := (-1215014954632512255577423732107294370843/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1144387656099180104718460148130600000000000000)
      constant := (9378901441164587911269371154809603157427355140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree028.table
  base := (-12151477065194287369566273004164925047721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-5158668202003060510668630451198200000000000000)
      constant := (42356788899136176714533937148650166126465578311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129414649464505424679/50000000000000000000)
  centralHi := (258829298929010849359/100000000000000000000)
  directionLo := (32947357067070687459/12500000000000000000)
  directionHi := (263578856536565499673/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree029.table
  base := (-5920962650479481077620192349081554592191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1180890041190838599362011838513550000000000000)
      constant := (10015439951677093161053364722726698921267744036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree029.table
  base := (-11843001613564797204014937078033934255811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-5323247640256836237973025907371850000000000000)
      constant := (45231674579011068200109424122631389068229167501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32947357067070687459/12500000000000000000)
  centralHi := (263578856536565499673/100000000000000000000)
  directionLo := (268244331239568785143/100000000000000000000)
  directionHi := (33530541404946098143/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree030.table
  base := (-11452785042719640703109244106226756120373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-135265825142499677111729280988500000000000000)
      constant := (1185928860840772490117263463512106875169827606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree030.table
  base := (-44740846357303092584185148038580627803/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-609758564278956885030824595949500000000000000)
      constant := (5355901993511716794252080399503848544327116032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268244331239568785143/100000000000000000000)
  centralHi := (33530541404946098143/12500000000000000000)
  directionLo := (68207509150021203273/25000000000000000000)
  directionHi := (272830036600084813093/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree031.table
  base := (-2745909044941555945854649931023287318131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1253894811374155588649115219279450000000000000)
      constant := (11352643041819431657697081855982980775459984552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree031.table
  base := (-10984341270202542387246464791584599310199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-5652406516764387692581816819719150000000000000)
      constant := (51271039683209416445656864547355923454446656409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68207509150021203273/25000000000000000000)
  centralHi := (272830036600084813093/100000000000000000000)
  directionLo := (138669964754668250493/50000000000000000000)
  directionHi := (277339929509336500987/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree032.table
  base := (-10435189120323864066170227394665793852579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1290397196465814083292666909662400000000000000)
      constant := (12053275909012501458341121965776161108901746442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree032.table
  base := (-13044698634476861050950085301984388689/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-5816985955018163419886212275892800000000000000)
      constant := (54435377750042458280791624170170607246505599200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138669964754668250493/50000000000000000000)
  centralHi := (277339929509336500987/100000000000000000000)
  directionLo := (56355530031855386649/20000000000000000000)
  directionHi := (140888825079638466623/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree033.table
  base := (-9808000082719274410286174754805608256491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1980000000000000000000000000000000000000000
      center := (7731)
      previous := (0)
      next := (6525)
      square := (339952364066668168973706080400000000000000)
      linear := (-13403026076338106847840591919650000000000000)
      constant := (129042903496510319065928298214250052065214782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree033.table
  base := (-4904230042306352550892082527228871924269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (34857)
      previous := (0)
      next := (29295)
      square := (1529785638300006760381677361800000000000000)
      linear := (-60419852457292314618086946788550000000000000)
      constant := (582788723056651295221270855010381275230952642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56355530031855386649/20000000000000000000)
  centralHi := (140888825079638466623/50000000000000000000)
  directionLo := (57229311286551048463/20000000000000000000)
  directionHi := (71536639108188810579/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree034.table
  base := (-1137813072953083369310264048748602070383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1363401966649131072579770290428300000000000000)
      constant := (13518549116247683342911315953470257967730819472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree034.table
  base := (-9102875614282003060964521925539026980949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-6146144831525714874495003188240100000000000000)
      constant := (61053119179324810802937463540497765469037469659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57229311286551048463/20000000000000000000)
  centralHi := (71536639108188810579/25000000000000000000)
  directionLo := (29044975363625995193/10000000000000000000)
  directionHi := (290449753636259951931/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree035.table
  base := (-259970113841625852877931917365516288351/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1399904351740789567223321980811250000000000000)
      constant := (14283174234620064022893797276305128978403798336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree035.table
  base := (-831934265291643811259047957735055991223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-6310724269779490601799398644413750000000000000)
      constant := (64506454799969002779611702397787968835702103930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29044975363625995193/10000000000000000000)
  centralHi := (290449753636259951931/100000000000000000000)
  directionLo := (294690120323712620033/100000000000000000000)
  directionHi := (147345060161856310017/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree036.table
  base := (-74578842939727499462602396907346466713/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-17733416504104297060084860138200000000000000)
      constant := (186038488480053106568293531213317215505545400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree036.table
  base := (-3729062533545138751091406151214349651849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-79942021086830448507454248155400000000000000)
      constant := (840198360112770427376152953559605146458272878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294690120323712620033/100000000000000000000)
  centralHi := (147345060161856310017/50000000000000000000)
  directionLo := (59774066164330611787/20000000000000000000)
  directionHi := (37358791352706632367/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree037.table
  base := (-814904454889201345405855719920259323887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1472909121924106556510425361577150000000000000)
      constant := (15876375014215802630186756302494751801365336208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree037.table
  base := (-1629857342159949978951719744130740829067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-6639883146287042056408189556761050000000000000)
      constant := (71701938070618450009888384821046920303835315988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59774066164330611787/20000000000000000000)
  centralHi := (37358791352706632367/12500000000000000000)
  directionLo := (302992874956630726109/100000000000000000000)
  directionHi := (30299287495663072611/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree038.table
  base := (-5503261419584221357461954050538979177937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1509411507015765051153977051960100000000000000)
      constant := (16704943366958984170493106318340703680154078926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree038.table
  base := (-5503417183480995547175102700237911887341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-6804462584540817783712585012934700000000000000)
      constant := (75444053247560715377874510016663451530329537731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302992874956630726109/100000000000000000000)
  centralHi := (30299287495663072611/10000000000000000000)
  directionLo := (61412015079632286451/20000000000000000000)
  directionHi := (4797813678096272379/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree039.table
  base := (-4410089857047592732386692592555191376459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-171768210234158171755280971371450000000000000)
      constant := (1950535567968089767917843222689556980682072298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree039.table
  base := (-4410215008901674639912373100115541442861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-774338002532732612335220052123150000000000000)
      constant := (8809155726862437807516317437345551953318519339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61412015079632286451/20000000000000000000)
  centralHi := (4797813678096272379/1562500000000000000)
  directionLo := (3888426287003938441/1250000000000000000)
  directionHi := (311074102960315075281/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree040.table
  base := (-1619910679735161756804893292002235461069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1582416277199082040441080432726000000000000000)
      constant := (18426003280280312586230414168747844360984250924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree040.table
  base := (-5183874958986125751392203205352707403/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-7133621461048369238321375925282000000000000000)
      constant := (83216974220137316357249773438296901895430483125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3888426287003938441/1250000000000000000)
  centralHi := (311074102960315075281/100000000000000000000)
  directionLo := (157518495074074416533/50000000000000000000)
  directionHi := (315036990148148833067/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree041.table
  base := (-498133638742241103197369957893577649929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1618918662290740535084632123108950000000000000)
      constant := (19318491331393157568352656916867510051124366968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree041.table
  base := (-1992615192303243327372620910545761939583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-7298200899302144965625771381455650000000000000)
      constant := (87247764447598281974312265431561228260071323153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157518495074074416533/50000000000000000000)
  centralHi := (315036990148148833067/100000000000000000000)
  directionLo := (318950643188950076033/100000000000000000000)
  directionHi := (159475321594475038017/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree042.table
  base := (-167072754135938192567102789179982742707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-183935671931377669969798201499100000000000000)
      constant := (2248031450899710245031324538042982740345536616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree042.table
  base := (-20886115152186076631444170042168634807/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-829197815283991188103351870847700000000000000)
      constant := (10152751874946635339983977750935972066728210976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318950643188950076033/100000000000000000000)
  centralHi := (159475321594475038017/50000000000000000000)
  directionLo := (10088026648450562921/3125000000000000000)
  directionHi := (322816852750418013473/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree043.table
  base := (29314441528451610165739355723344764529/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1691923432474057524371735503874850000000000000)
      constant := (21167377515231738494243611588704242289357436450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree043.table
  base := (183202301465355562873304857108012686551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-7627359775809696420234562293802950000000000000)
      constant := (95597977313878660353096527684934097139271908636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10088026648450562921/3125000000000000000)
  centralHi := (322816852750418013473/100000000000000000000)
  directionLo := (637963483431247193/195312500000000000)
  directionHi := (326637303516798562817/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree044.table
  base := (2210883850011114927961869299425331607669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-157129619778701456274117017659800000000000000)
      constant := (2011252178421699171852870109198800940924866158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree044.table
  base := (2210842328294840524569434435988135471211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-708358110369406558867177977270600000000000000)
      constant := (9083399317142724837232776013556638858343641009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637963483431247193/195312500000000000)
  centralHi := (326637303516798562817/100000000000000000000)
  directionLo := (165206791384135679087/50000000000000000000)
  directionHi := (13216543310730854327/4000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree045.table
  base := (3765747849258710793511932875505638744983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-21789237069844129798257270180750000000000000)
      constant := (285203355811049491292647629769739552076285886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree045.table
  base := (753142920866728447687100474119525983189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-98228625337249973763498187730250000000000000)
      constant := (1288061849798071956943003712496815193978464105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165206791384135679087/50000000000000000000)
  centralHi := (13216543310730854327/4000000000000000000)
  directionLo := (167073594043766703799/50000000000000000000)
  directionHi := (334147188087533407599/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree046.table
  base := (5397429879553219010594689345198114394577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1801430587749033008302390575023700000000000000)
      constant := (24100470635488922572226691509807892188362498354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree046.table
  base := (5397403274695733613735997278672804604911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-8121098090571023602147748662323900000000000000)
      constant := (108844827341526712051381658606351086921394594399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167073594043766703799/50000000000000000000)
  centralHi := (334147188087533407599/100000000000000000000)
  directionLo := (337839534299710916233/100000000000000000000)
  directionHi := (168919767149855458117/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree047.table
  base := (7105911806564664302071723788577425081911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1837932972840691502945942265406650000000000000)
      constant := (25120770051551296047565804487303399373955619422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree047.table
  base := (710589052560288862084088209087118168933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-8285677528824799329452144118497550000000000000)
      constant := (113452843440883060286707973891600565440634109970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337839534299710916233/100000000000000000000)
  centralHi := (168919767149855458117/50000000000000000000)
  directionLo := (85372989934201990141/25000000000000000000)
  directionHi := (68298391947361592113/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree048.table
  base := (8891179428676311967328031993620460310163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-208270595325816666398832661754400000000000000)
      constant := (2906929976722448665235593514585705362555535014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree048.table
  base := (8891162413951002285366096888914649474767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-938917440786508339639615508296800000000000000)
      constant := (13128561877978400358075200336295452479502191367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85372989934201990141/25000000000000000000)
  centralHi := (68298391947361592113/20000000000000000000)
  directionLo := (43138216488168474893/12500000000000000000)
  directionHi := (69021146381069559829/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree049.table
  base := (5376610811966194938811966915322929599691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1910937743024008492233045646172550000000000000)
      constant := (27225269634328571345622747731809724819526285964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree049.table
  base := (10753208026086508433348037778598878434757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-8614836405332350784060935030844850000000000000)
      constant := (122957466761611873440648990475622737842851480213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43138216488168474893/12500000000000000000)
  centralHi := (69021146381069559829/20000000000000000000)
  directionLo := (348682052625261902091/100000000000000000000)
  directionHi := (87170513156315475523/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree050.table
  base := (1269202968203030601075762247516372077461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-1947440128115666986876597336555500000000000000)
      constant := (28309469412291544714253822971544878004623905220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree050.table
  base := (6346009409707683667530882609744675758799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-8779415843586126511365330487018500000000000000)
      constant := (127854072266768193290105229046569373708015801982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348682052625261902091/100000000000000000000)
  centralHi := (87170513156315475523/25000000000000000000)
  directionLo := (88055515674774041639/25000000000000000000)
  directionHi := (352222062699096166557/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree051.table
  base := (14707596781216711549472217714588775008033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-220438057023036164613349891882050000000000000)
      constant := (3268329887852327661055299776061079039467495874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree051.table
  base := (14707588107106879788309643331770757343861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-993777253537766915407747327021350000000000000)
      constant := (14760763647492879291679874164019594567727181661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88055515674774041639/25000000000000000000)
  centralHi := (352222062699096166557/100000000000000000000)
  directionLo := (177863423081479959293/50000000000000000000)
  directionHi := (355726846162959918587/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree052.table
  base := (16799917578654454481762893883736816626147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2020444898298983976163700717321400000000000000)
      constant := (30541768264736490197615054178135284079505733494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree052.table
  base := (16799910654791584298495780010631098522607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-9108574720093677965974121399365800000000000000)
      constant := (137935867981896538616713096717770308569580640863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177863423081479959293/50000000000000000000)
  centralHi := (355726846162959918587/100000000000000000000)
  directionLo := (359197434164118539261/100000000000000000000)
  directionHi := (179598717082059269631/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree053.table
  base := (1896898788964611411310561005955220221629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2056947283390642470807252407704350000000000000)
      constant := (31689867152459729618151831302127859455343716580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree053.table
  base := (1185561397807009636150554804586388902463/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-9273154158347453693278516855539450000000000000)
      constant := (143121057368708634035135695352312706834157740272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359197434164118539261/100000000000000000000)
  centralHi := (179598717082059269631/50000000000000000000)
  directionLo := (362634808504542753027/100000000000000000000)
  directionHi := (90658702126135688257/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree054.table
  base := (21214804436439256506244466602535400693641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-25845057635583962536429680223300000000000000)
      constant := (405669945550495851865060977923382316967861122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree054.table
  base := (10607400014838315521064893160664037833867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (14201)
      previous := (0)
      next := (11935)
      square := (623246000788891643118461147400000000000000)
      linear := (-38838409862556499673180709101700000000000000)
      constant := (610709632530518843716556054688354591467387442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362634808504542753027/100000000000000000000)
  centralHi := (90658702126135688257/25000000000000000000)
  directionLo := (183019952442463574161/50000000000000000000)
  directionHi := (366039904884927148323/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree055.table
  base := (23537364651519715411563333845448631971013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-193632004870359950917668708042750000000000000)
      constant := (3095451229618125514504036593945128524672345166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree055.table
  base := (11768680568851938806434016086623058196913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-872937548623182286171573433444250000000000000)
      constant := (13980001615362950440238814855924838732362090694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183019952442463574161/50000000000000000000)
  centralHi := (366039904884927148323/100000000000000000000)
  directionLo := (18470680793977697497/5000000000000000000)
  directionHi := (369413615879553949941/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree056.table
  base := (25328775901927110814203016452775415801/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2166454438665617954737907478853200000000000000)
      constant := (35261960921661600029952271500652578989343950848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree056.table
  base := (25936663722691742689707751772152416226237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-9766892473108780875191703224060400000000000000)
      constant := (159253788387492215038365634400911992482900139533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18470680793977697497/5000000000000000000)
  centralHi := (369413615879553949941/100000000000000000000)
  directionLo := (4659459920860040561/1250000000000000000)
  directionHi := (372756793668803244881/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree057.table
  base := (28412708476860734924594027642044174466581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-244772980417475161042384352137350000000000000)
      constant := (4055028638476575246879716054622214399488213418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree057.table
  base := (1136508249798988380376503285790898653299/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1103496879040284066944010964470450000000000000)
      constant := (18313750269400333782463424211664099317524587475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4659459920860040561/1250000000000000000)
  centralHi := (372756793668803244881/100000000000000000000)
  directionLo := (15042810102120514397/4000000000000000000)
  directionHi := (188035126276506429963/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree058.table
  base := (7741372319189164250274628980371556844783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2239459208848934944025010859619100000000000000)
      constant := (37749853975480989481327296883349341779085745464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree058.table
  base := (15482743749411416058755648973514620240711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-10096051349616332329800494136407700000000000000)
      constant := (170489909773968589051344561610992239773625753198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15042810102120514397/4000000000000000000)
  centralHi := (188035126276506429963/50000000000000000000)
  directionLo := (75870954253739815767/20000000000000000000)
  directionHi := (94838692817174769709/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree059.table
  base := (16797503977889575810977334316443997185937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2275961593940593438668562550002050000000000000)
      constant := (39025749590272455113036133443490337653177474148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree059.table
  base := (4199375817485920541040699658008958642833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-10260630787870108057104889592581350000000000000)
      constant := (176252260352288911513594368185350932238405248776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75870954253739815767/20000000000000000000)
  centralHi := (94838692817174769709/25000000000000000000)
  directionLo := (191305547562902051833/50000000000000000000)
  directionHi := (382611095125804103667/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree060.table
  base := (36301263755663177273952394230000992025499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-256940442114694659256901582265000000000000000)
      constant := (4480327175088895863700223328614817160631536822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree060.table
  base := (18150631314207211226805260238874345888233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1158356691791542642712142783195000000000000000)
      constant := (20234533788256780122518204220566164928101143266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191305547562902051833/50000000000000000000)
  centralHi := (382611095125804103667/100000000000000000000)
  directionLo := (77167987596517569769/20000000000000000000)
  directionHi := (192919968991293924423/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree061.table
  base := (19542128040999385420856972191438629750517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2348966364123910427955665930767950000000000000)
      constant := (41641438920412188365137291802714752228239268468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree061.table
  base := (9771063796199921334038693470466002239673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-10589789664377659511713680504928650000000000000)
      constant := (188065540948908600253596520003696026741237262628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77167987596517569769/20000000000000000000)
  centralHi := (192919968991293924423/50000000000000000000)
  directionLo := (389041984072988397537/100000000000000000000)
  directionHi := (194520992036494198769/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree062.table
  base := (20971992234354086496807489545367508416653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2385468749215568922599217621150900000000000000)
      constant := (42981232614972775650123478666339206549966464212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree062.table
  base := (41943983754801961537508246558020211233553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-10754369102631435239018075961102300000000000000)
      constant := (194116470876013487710798168407151642312700476577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389041984072988397537/100000000000000000000)
  centralHi := (194520992036494198769/50000000000000000000)
  directionLo := (98054472424925459963/25000000000000000000)
  directionHi := (392217889699701839853/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree063.table
  base := (11220112137556926101712146802947071527841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-29900878201323795274602090265850000000000000)
      constant := (547436119164395622051542092298832452738950088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree063.table
  base := (22440223991158199037139132014541144932027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-134801833838089024275586066879950000000000000)
      constant := (2472390047459432475277243194722329988661954806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98054472424925459963/25000000000000000000)
  centralHi := (392217889699701839853/100000000000000000000)
  directionLo := (98842071201212062377/25000000000000000000)
  directionHi := (395368284804848249509/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree064.table
  base := (23946824019861559196795400730698062844417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2458473519398885911886321001916800000000000000)
      constant := (45724718026819472669716858825599886855752524068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree064.table
  base := (47893647588064351609191169370826841944911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-11083527979138986693626866873449600000000000000)
      constant := (206506909828875338763434539096138464901118654399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98842071201212062377/25000000000000000000)
  centralHi := (395368284804848249509/100000000000000000000)
  directionLo := (199246887214435372623/50000000000000000000)
  directionHi := (398493774428870745247/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree065.table
  base := (25491791356014843534442051690758873845387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2494975904490544406529872692299750000000000000)
      constant := (47128409734069378504748389437708065577734551948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree065.table
  base := (10196716470582805654579080126412613783441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-11248107417392762420931262329623250000000000000)
      constant := (212846418810668016103310057449888260621117735845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199246887214435372623/50000000000000000000)
  centralHi := (398493774428870745247/100000000000000000000)
  directionLo := (200797470033618601161/50000000000000000000)
  directionHi := (401594940067237202323/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree066.table
  base := (54150252390292169291558970505780735509289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1980000000000000000000000000000000000000000
      center := (7731)
      previous := (0)
      next := (6525)
      square := (339952364066668168973706080400000000000000)
      linear := (-25570487773557605062357822047300000000000000)
      constant := (490438391622212590448689861950950835630839222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree066.table
  base := (2707512605241273709797808672375624771009/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (34857)
      previous := (0)
      next := (29295)
      square := (1529785638300006760381677361800000000000000)
      linear := (-115279665208550890386218765513100000000000000)
      constant := (2214970916913298891173881625653346133419380380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200797470033618601161/50000000000000000000)
  centralHi := (401594940067237202323/100000000000000000000)
  directionLo := (80934468186712133629/20000000000000000000)
  directionHi := (202336170466780334073/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree067.table
  base := (57393656935502117964828993148977068269427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2567980674673861395816976073065650000000000000)
      constant := (49999691133683632938741372309258640679717308054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree067.table
  base := (57393656708632233112630723778040135683439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-11577266293900313875540053241970550000000000000)
      constant := (225814015708198163191402306092389426703500470751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80934468186712133629/20000000000000000000)
  centralHi := (202336170466780334073/50000000000000000000)
  directionLo := (101931628784227249329/25000000000000000000)
  directionHi := (407726515136908997317/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree068.table
  base := (1897306132447002195421174071293972656933/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2604483059765519890460527763448600000000000000)
      constant := (51467280821179552175215701552667417464678421312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree068.table
  base := (15178449014510795434089523687184748322613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-11741845732154089602844448698144200000000000000)
      constant := (232442103602636901304889877463034067859157480468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101931628784227249329/25000000000000000000)
  centralHi := (407726515136908997317/100000000000000000000)
  directionLo := (25672373798770187749/6250000000000000000)
  directionHi := (82151596156064600797/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree069.table
  base := (8013833776572310938170595785373781863747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-293442827206353153900453272647950000000000000)
      constant := (5884018870155409885242670782816182462693927728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree069.table
  base := (64110670069382040403683585129253736415869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1322936130045318370016538239368650000000000000)
      constant := (26574042716705755957093702145642975245611932069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25672373798770187749/6250000000000000000)
  centralHi := (82151596156064600797/20000000000000000000)
  directionLo := (3232556538960107683/781250000000000000)
  directionHi := (16550689479475751337/4000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree070.table
  base := (67584278790416063670835722476367498948909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2677487829948836879747631144214500000000000000)
      constant := (54466358163009885097461044247499724464396514218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree070.table
  base := (13516855735337384495948258531107518163251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-12071004608661641057453239610491500000000000000)
      constant := (245986858245524438060087745262838252848311037295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3232556538960107683/781250000000000000)
  centralHi := (16550689479475751337/4000000000000000000)
  directionLo := (208377382429576821133/50000000000000000000)
  directionHi := (416754764859153642267/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree071.table
  base := (35567310959090808200049927195092702902249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2713990215040495374391182834597450000000000000)
      constant := (55997845814961783721626128122322194012079769796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree071.table
  base := (71134621827874360370623935656363335482529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-12235584046915416784757635066665150000000000000)
      constant := (252903524983560574050632187910251212834578400561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208377382429576821133/50000000000000000000)
  centralHi := (416754764859153642267/100000000000000000000)
  directionLo := (83944205675400506277/20000000000000000000)
  directionHi := (209860514188501265693/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree072.table
  base := (18690424888357809227740436752839642956633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-33956698767063628012774500308400000000000000)
      constant := (710501639338548139996675236354648774382020744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree072.table
  base := (37380849740868241131812020187644887227793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-153088438088508549531630006454800000000000000)
      constant := (3208844255071917363219130045684490564382133154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83944205675400506277/20000000000000000000)
  centralHi := (209860514188501265693/50000000000000000000)
  directionLo := (105666618809728849967/25000000000000000000)
  directionHi := (422666475238915399869/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree073.table
  base := (9808188957812204584847049002612055344661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2786994985223812363678286215363350000000000000)
      constant := (59124719076731785762114650861643941758428359376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree073.table
  base := (78465511605590288867123787763095391526493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-12564742923422968239366425979012450000000000000)
      constant := (267025437274435700485925466432903040766160421037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105666618809728849967/25000000000000000000)
  centralHi := (422666475238915399869/100000000000000000000)
  directionLo := (106397884412687221159/25000000000000000000)
  directionHi := (425591537650748884637/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree074.table
  base := (20561514554649692816651036247981636625829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2823497370315470858321837905746300000000000000)
      constant := (60720104685364961353725107363018812914558000232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree074.table
  base := (82246058173437327776930524216704708046969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-12729322361676743966670821435186100000000000000)
      constant := (274230682822098458758038556325955443092115088521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106397884412687221159/25000000000000000000)
  centralHi := (425591537650748884637/100000000000000000000)
  directionLo := (428496633066082476159/100000000000000000000)
  directionHi := (669525989165753869/156250000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree075.table
  base := (3444133568014250250954794027850781496137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-317777750600792150329487732903250000000000000)
      constant := (6926309956878096335949109939563154739964659650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree075.table
  base := (17220667832904571899691513821117786360637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1432655755547835521552801876817750000000000000)
      constant := (31281346811331425157890089651984736495603016185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428496633066082476159/100000000000000000000)
  centralHi := (669525989165753869/156250000000000000)
  directionLo := (43138216488168474893/10000000000000000000)
  directionHi := (431382164881684748931/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree076.table
  base := (90037354590634706292428825658444270503897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-2896502140498787847608941286512200000000000000)
      constant := (63974773856009614946794845055306299590417388994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree076.table
  base := (45018677281103856147792284121673742089037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-13058481238184295421279612347533400000000000000)
      constant := (288929752712621078775170777736196388231863729466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43138216488168474893/10000000000000000000)
  centralHi := (431382164881684748931/100000000000000000000)
  directionLo := (54281065386423130147/12500000000000000000)
  directionHi := (434248523091385041177/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree077.table
  base := (47024052187816202022002348786142381322963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-266636775053676940204772088808650000000000000)
      constant := (5966732492492242169217718246435188009535040132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree077.table
  base := (94048104353084887637728813293203400896579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-1202096425130733740780364345791550000000000000)
      constant := (26947597913893690717012208982843451196789667001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54281065386423130147/12500000000000000000)
  centralHi := (434248523091385041177/100000000000000000000)
  directionLo := (109274021225337820439/25000000000000000000)
  directionHi := (437096084901351281757/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree078.table
  base := (24533897136042200451032916254554062258243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-329945212298011648544004963030900000000000000)
      constant := (7479404477322094741205241975898243740393813016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree078.table
  base := (2453389713157193565646746754285016799847/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1487515568299094097320933695542300000000000000)
      constant := (33779288257961427561491297402557035486212017880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109274021225337820439/25000000000000000000)
  centralHi := (437096084901351281757/100000000000000000000)
  directionLo := (439925215309522134879/100000000000000000000)
  directionHi := (2749532595684513343/625000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree079.table
  base := (102299807087126177813649533427125180033943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3006009295773763331539596357661050000000000000)
      constant := (69016522491283455793228618138253912466525350686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree079.table
  base := (10229980707294813149121234214143806572061/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-13552219552945622603192798716054350000000000000)
      constant := (311699804518305579003913238020672419714149287490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439925215309522134879/100000000000000000000)
  centralHi := (2749532595684513343/625000000000000000)
  directionLo := (221368133825856657097/50000000000000000000)
  directionHi := (88547253530342662839/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree080.table
  base := (10654075999701202690707891346219935798281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3042511680865421826183148048044000000000000000)
      constant := (70739704003421605142285494786516031815179041620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree080.table
  base := (106540759985771932500081020478428241802267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-13716798991199398330497194172228000000000000000)
      constant := (319482207642145383554603226517841676781136169803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221368133825856657097/50000000000000000000)
  centralHi := (88547253530342662839/20000000000000000000)
  directionLo := (44552958411671121013/10000000000000000000)
  directionHi := (445529584116711210131/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree081.table
  base := (6928652954226000827738243623581243049717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-38012519332803460750946910350950000000000000)
      constant := (894866479409772416232965574469036260588504224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree081.table
  base := (27714611814676616302440003091224718329983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (14201)
      previous := (0)
      next := (11935)
      square := (623246000788891643118461147400000000000000)
      linear := (-57125014112976024929224648676550000000000000)
      constant := (1347163801204273089779095127263311416015135316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44552958411671121013/10000000000000000000)
  centralHi := (445529584116711210131/100000000000000000000)
  directionLo := (224152748116239794201/50000000000000000000)
  directionHi := (448305496232479588403/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree082.table
  base := (115252868893740989358638538937658936791813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3115516451048738815470251428809900000000000000)
      constant := (74249964977491463026369722973304109228993118426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree082.table
  base := (57626434443339921605991888713682735093829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-14045957867706949785105985084575300000000000000)
      constant := (335335592669337124760877211191296718259783124522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224152748116239794201/50000000000000000000)
  centralHi := (448305496232479588403/100000000000000000000)
  directionLo := (451064325325435031853/100000000000000000000)
  directionHi := (225532162662717515927/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree083.table
  base := (29931006217748007704896341147919088820589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3152018836140397310113803119192850000000000000)
      constant := (76037044439235147768068485117177682103744742312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree083.table
  base := (59862012432698321816502537132961652253899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-14210537305960725512410380540748950000000000000)
      constant := (343406574571862780432004141900133613142328353782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451064325325435031853/100000000000000000000)
  centralHi := (225532162662717515927/50000000000000000000)
  directionLo := (56725797869324027979/12500000000000000000)
  directionHi := (453806382954592223833/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree084.table
  base := (62135957597805458337953402651004816739821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-354280135692450644973039423286200000000000000)
      constant := (8649491468594327921432220367509051981718660276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree084.table
  base := (124271915191177668420856189452780556720307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1597235193801611248857197332991400000000000000)
      constant := (39063749933321198827637209779749252236415728907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56725797869324027979/12500000000000000000)
  centralHi := (453806382954592223833/100000000000000000000)
  directionLo := (114132992830559881313/25000000000000000000)
  directionHi := (456531971322239525253/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree085.table
  base := (128896539864346211744275182342358061037911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3225023606323714299400906499958750000000000000)
      constant := (79675101311769138968370628386122519899965131422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree085.table
  base := (128896539860834228654996696465243795897757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-14539696182468276967019171453096250000000000000)
      constant := (359837117153139880750077499060985424367345247213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114132992830559881313/25000000000000000000)
  centralHi := (456531971322239525253/100000000000000000000)
  directionLo := (459241383662677173719/100000000000000000000)
  directionHi := (11481034591566929343/2500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree086.table
  base := (33399474718587810348879024853514483175401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3261525991415372794044458190341700000000000000)
      constant := (81526078722439910278429343836554432346816841608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree086.table
  base := (26719579774313892412011730244221071358367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-14704275620722052694323566909269900000000000000)
      constant := (368196677831363345911584044050312619917250973515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459241383662677173719/100000000000000000000)
  centralHi := (11481034591566929343/2500000000000000000)
  directionLo := (461934904610433583053/100000000000000000000)
  directionHi := (230967452305216791527/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree087.table
  base := (138375992223103921119518057372546156744491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-366447597389670143187556653413850000000000000)
      constant := (9266483938812425258055436005849497716889501398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree087.table
  base := (138375992220900821053387175391822898675899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1652095006552869824625329151715950000000000000)
      constant := (41850270159371355765948457647026940604922486099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461934904610433583053/100000000000000000000)
  centralHi := (230967452305216791527/50000000000000000000)
  directionLo := (232306405274634266899/50000000000000000000)
  directionHi := (464612810549268533799/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree088.table
  base := (35807704977085928048432923940975583985727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (69579)
      previous := (0)
      next := (58725)
      square := (3059571276600013520763354723600000000000000)
      linear := (-303139160145335434848323779191600000000000000)
      constant := (7753811953849143547321814224616173962650262056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree088.table
  base := (17903852488324892774701161353948936313047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (313713)
      previous := (0)
      next := (263655)
      square := (13768070744700060843435096256200000000000000)
      linear := (-1366675863384509468084759801965200000000000000)
      constant := (35018579814716346947116953668228332162354591144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232306405274634266899/50000000000000000000)
  centralHi := (464612810549268533799/100000000000000000000)
  directionLo := (467275369943174529813/100000000000000000000)
  directionHi := (233637684971587264907/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree089.table
  base := (37040595482005499976735784882678505970513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3371033146690348277975113261490550000000000000)
      constant := (87206806851486008426983226712076335983635983304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree089.table
  base := (148162381926640704715529451552672575843209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-15198013935483379876236753277790850000000000000)
      constant := (393852517413797679099799516716087754617553622681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467275369943174529813/100000000000000000000)
  centralHi := (233637684971587264907/50000000000000000000)
  directionLo := (469922843650498369143/100000000000000000000)
  directionHi := (58740355456312296143/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree090.table
  base := (76585339140131496790461105253085344361649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (9449)
      previous := (0)
      next := (7975)
      square := (415497333859261095412307431600000000000000)
      linear := (-42068339898543293489119320393500000000000000)
      constant := (1100530636132238843122889713877962056671038116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree090.table
  base := (76585339139584732951719439028211930574563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (42603)
      previous := (0)
      next := (35805)
      square := (1869738002366674929355383442200000000000000)
      linear := (-189661646589347600043717885604500000000000000)
      constant := (4970331478888050250212638891224383084791398214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469922843650498369143/100000000000000000000)
  centralHi := (58740355456312296143/12500000000000000000)
  directionLo := (472555485222223249599/100000000000000000000)
  directionHi := (295347178263889531/62500000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree091.table
  base := (15825570896333287631508624063703935217421/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3444037916873665267262216642256450000000000000)
      constant := (91100455517982606339567255347714212568818864420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree091.table
  base := (158255708962467271926049500043541599496457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-15527172811990931330845544190138150000000000000)
      constant := (411437375090131433288902265376742195324982975513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472555485222223249599/100000000000000000000)
  centralHi := (295347178263889531/62500000000000000)
  directionLo := (237586770592688397197/50000000000000000000)
  directionHi := (95034708237075358879/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree092.table
  base := (163417473975615424719152584062862183410427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3480540301965323761905768332639400000000000000)
      constant := (93079228825268107355926471858717499519211190054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree092.table
  base := (163417473974930320435965462592613130919543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-15691752250244707058149939646311800000000000000)
      constant := (420374093314254298363573621312026361665281968487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237586770592688397197/50000000000000000000)
  centralHi := (95034708237075358879/20000000000000000000)
  directionLo := (238888625656230803977/50000000000000000000)
  directionHi := (95555450262492321591/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree093.table
  base := (168655973315592704469509452273505326340377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-390782520784109139616591113669150000000000000)
      constant := (10564366827615343865935586453194349288269341106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree093.table
  base := (168655973315050525569459593304170884037199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1761814632055386976161592789165050000000000000)
      constant := (47711889384685293193920478649426988209448587399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238888625656230803977/50000000000000000000)
  centralHi := (95555450262492321591/20000000000000000000)
  directionLo := (96073369775548357811/20000000000000000000)
  directionHi := (3752866006857357727/781250000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree094.table
  base := (86985603490914874742664169705791762553261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3553545072148640751192871713405300000000000000)
      constant := (97100673387764440446932273635992679009138044244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree094.table
  base := (86985603490700364348814449846978469361287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-16020911126752258512758730558659100000000000000)
      constant := (438536108533745566198537420911147885107779529966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96073369775548357811/20000000000000000000)
  centralHi := (3752866006857357727/781250000000000000)
  directionLo := (482942560901160727803/100000000000000000000)
  directionHi := (120735640225290181951/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree095.table
  base := (35872634994592473801082057213842520852967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3590047457240299245836423403788250000000000000)
      constant := (99143344642920403449161436528134760156299295670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree095.table
  base := (35872634994524585504384273642956000591777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-16185490565006034240063126014832750000000000000)
      constant := (447761405528868292698579985947957138656000286965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482942560901160727803/100000000000000000000)
  centralHi := (120735640225290181951/25000000000000000000)
  directionLo := (30344038023788252271/6250000000000000000)
  directionHi := (485504608380612036337/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree096.table
  base := (46207969321921853014439716673594038598893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (85041)
      previous := (0)
      next := (71775)
      square := (3739476004733349858710766884400000000000000)
      linear := (-402949982481328637831108343796800000000000000)
      constant := (11245257245997826603861632535722751264273555816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree096.table
  base := (184831877287418875520663178862590133203243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (383427)
      previous := (0)
      next := (322245)
      square := (16827642021300074364198450979800000000000000)
      linear := (-1816674444806645551929724607889600000000000000)
      constant := (50786988383046811246442408551837045895524984643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30344038023788252271/6250000000000000000)
  centralHi := (485504608380612036337/100000000000000000000)
  directionLo := (488053206513236197763/100000000000000000000)
  directionHi := (122013301628309049441/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree097.table
  base := (190377313924754963871791308048566836831299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3663052227423616235123526784554150000000000000)
      constant := (103292585100920047574379078995081461823067122998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree097.table
  base := (95188656962271272099502412536380427518459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-16514649441513585694671916927180050000000000000)
      constant := (466500578289294680829240313842317571636951499862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell189.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488053206513236197763/100000000000000000000)
  centralHi := (122013301628309049441/25000000000000000000)
  directionLo := (245294282453185045897/50000000000000000000)
  directionHi := (98117712981274018359/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree098.table
  base := (195999484882962062396564923973212569733987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (765369)
      previous := (0)
      next := (645975)
      square := (33655284042600148728396901959600000000000000)
      linear := (-3699554612515274729767078474937100000000000000)
      constant := (105399154303715647405912016514784531541925613174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1291
  qDenominator := 2376
  table := BinomialMassData.Q1291_2376.Degree098.table
  base := (195999484882794050537443303231732493398759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3450843)
      previous := (0)
      next := (2900205)
      square := (151448778191700669277786058818200000000000000)
      linear := (-16679228879767361421976312383353700000000000000)
      constant := (476014454054382591051088556129561129010211132631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1291_2376.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell189.Kernel098
