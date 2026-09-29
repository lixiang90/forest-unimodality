import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell030.Parameters
import ForestUnimodality.BinomialMassData.Q22_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree000.table
  base := (290162235118569672022381671/6250000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2525)
      previous := (2222)
      next := (0)
      square := (91574683663089044005634066300000000000000)
      linear := (374677303852372630688094543500000000000000)
      constant := (21820200080916439336083101659200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree000.table
  base := (290162235118569672022381671/6250000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (191395)
      previous := (169377)
      next := (0)
      square := (6959675958394767344428189038800000000000000)
      linear := (28475475092780319932295185306000000000000000)
      constant := (1658335206149649389542315726099200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree001.table
  base := (70935222709940500019749877449029603284191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (13580547199885595706092544627300000000000000)
      constant := (619483751582259402795089430546225574619111676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree001.table
  base := (28320427482415687654290979385518896184897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (19592910966738813281236563969224200000000000000)
      constant := (892795403799941411952555502828881854749997110120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24949019999060795503/50000000000000000000)
  directionHi := (49898039998121591007/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree002.table
  base := (11232366285893890857904486591029139140579/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (9551261118709677769844645710100000000000000)
      constant := (384283050247038652714370387613733893784624176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree002.table
  base := (179102531716594261203731893637802705917557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (13757222675624800862933527460190400000000000000)
      constant := (552903388256542221407800748392471620124999648372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/50000000000000000000)
  centralHi := (49898039998121591007/100000000000000000000)
  directionLo := (70566484901178720193/100000000000000000000)
  directionHi := (35283242450589360097/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree003.table
  base := (118366864017397014766259942234315445059029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (5521975037533759833596746792900000000000000)
      constant := (245230920177969494454712312797002818135395061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree003.table
  base := (1472829381610789643133471520990968798891/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (7921534384510788444630490951156600000000000000)
      constant := (352355946253960457681766658797895389866185298880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70566484901178720193/100000000000000000000)
  centralHi := (35283242450589360097/50000000000000000000)
  directionLo := (21606485118712660533/25000000000000000000)
  directionHi := (86425940474850642133/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree004.table
  base := (40509491230581704905257462279980057753587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (1492688956357841897348847875700000000000000)
      constant := (161087719949338660702356642342551895155347366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree004.table
  base := (8058457202355225389194802326654839837851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (2085846093396776026327454442122800000000000000)
      constant := (231213113221338335370705538558437414954177683960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21606485118712660533/25000000000000000000)
  centralHi := (86425940474850642133/100000000000000000000)
  directionLo := (24949019999060795503/25000000000000000000)
  directionHi := (99796079996243182013/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree005.table
  base := (57341630505520000375328192096876798693627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-2536597124818076038899051041500000000000000)
      constant := (109028768412366253846349410647000848314222043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree005.table
  base := (456015136678065667865587527082691099497/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-3749842197717236391975582066911000000000000000)
      constant := (156379785590983971606367933452480592301391576500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/25000000000000000000)
  centralHi := (99796079996243182013/100000000000000000000)
  directionLo := (55787704689901678031/50000000000000000000)
  directionHi := (111575409379803356063/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree006.table
  base := (2599562961801790964375315829039136752009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-6565883205993993975146949958700000000000000)
      constant := (76370427684593642439886044009159249363006096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree006.table
  base := (4132628777900092423537698091391095156997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-9585530488831248810278618575944800000000000000)
      constant := (109508183617774242276319750433403397674084026120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55787704689901678031/50000000000000000000)
  centralHi := (111575409379803356063/100000000000000000000)
  directionLo := (122224737160383588507/100000000000000000000)
  directionHi := (30556184290095897127/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree007.table
  base := (3820240265311705138408610470400184138943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-10595169287169911911394848875900000000000000)
      constant := (56019176872212850370152479350312054103400696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree007.table
  base := (30348105776122621929647372041270983228427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-15421218779945261228581655084978600000000000000)
      constant := (80360167947785183859433926618459742218103530892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122224737160383588507/100000000000000000000)
  centralHi := (30556184290095897127/25000000000000000000)
  directionLo := (132017804744583580809/100000000000000000000)
  directionHi := (13201780474458358081/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree008.table
  base := (22435668446172953469237730845005691906553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-14624455368345829847642747793100000000000000)
      constant := (43970747846128390938367483051017573421575577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree008.table
  base := (22259325616462274283056576211120322793657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-21256907071059273646884691594012400000000000000)
      constant := (63168522150871890172655993027828361165915923972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132017804744583580809/100000000000000000000)
  centralHi := (13201780474458358081/10000000000000000000)
  directionLo := (141132969802357440387/100000000000000000000)
  directionHi := (35283242450589360097/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree009.table
  base := (8088456000678121432498490503133975089411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-18653741449521747783890646710300000000000000)
      constant := (37933669008390901765660673881445901945017798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree009.table
  base := (16027232170057105659352081061145441205549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-27092595362173286065187728103046200000000000000)
      constant := (54639095636339619342570230738251008775695378004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141132969802357440387/100000000000000000000)
  centralHi := (35283242450589360097/25000000000000000000)
  directionLo := (74847059997182386509/50000000000000000000)
  directionHi := (149694119994364773019/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree010.table
  base := (559016230104771587613040084552632578179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-22683027530697665720138545627500000000000000)
      constant := (36570770396241079561122647725535307303948220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree010.table
  base := (5525055081396885410016685345129567193951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-32928283653287298483490764612080000000000000000)
      constant := (52852539429682719180788648130503325833992247992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74847059997182386509/50000000000000000000)
  centralHi := (149694119994364773019/100000000000000000000)
  directionLo := (39447864293062036961/25000000000000000000)
  directionHi := (31558291434449629569/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree011.table
  base := (7083042303479557628684643650691194063419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-26712313611873583656386444544700000000000000)
      constant := (39080485555370608157074295292976847686092571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree011.table
  base := (3483817823025553996304133656655785938091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-38763971944401310901793801121113800000000000000)
      constant := (56659493640885202350062786474225523724357838872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39447864293062036961/25000000000000000000)
  centralHi := (31558291434449629569/20000000000000000000)
  directionLo := (165493076447915378051/100000000000000000000)
  directionHi := (41373269111978844513/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree012.table
  base := (3659766479268159133754996932540782880721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-30741599693049501592634343461900000000000000)
      constant := (44965129820414308408141273098382589383512689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree012.table
  base := (1778092280665339179434719154043623416381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-44599660235515323320096837630147600000000000000)
      constant := (65346643142644982701830169000405067598156896552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165493076447915378051/100000000000000000000)
  centralHi := (41373269111978844513/25000000000000000000)
  directionLo := (34570376189940256853/20000000000000000000)
  directionHi := (86425940474850642133/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree013.table
  base := (764486340958250969782598909700763798133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-34770885774225419528882242379100000000000000)
      constant := (53902165359569085791727999998928987230075797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree013.table
  base := (670801163345938044809918738554638083309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-50435348526629335738399874139181400000000000000)
      constant := (78451608678470023732958874983948355339586714964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34570376189940256853/20000000000000000000)
  centralHi := (86425940474850642133/50000000000000000000)
  directionLo := (179909941758380456363/100000000000000000000)
  directionHi := (44977485439595114091/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree014.table
  base := (-851041796400034475594196165200960950077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-38800171855401337465130141296300000000000000)
      constant := (65672270544533006595540021209742154522559814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree014.table
  base := (-1787158608208835654615849011256740792001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-56271036817743348156702910648215200000000000000)
      constant := (95659735819373372381785404923663193248638378204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179909941758380456363/100000000000000000000)
  centralHi := (44977485439595114091/25000000000000000000)
  directionLo := (186701369944513235327/100000000000000000000)
  directionHi := (1458604452691509651/781250000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree015.table
  base := (-3810853675544860440248462237285764268693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-42829457936577255401378040213500000000000000)
      constant := (80118804404340496696878454372835746730457163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree015.table
  base := (-1944113298127787485088813021270442716233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-62106725108857360575005947157249000000000000000)
      constant := (116746042374930020906329297938005378811061683064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186701369944513235327/100000000000000000000)
  centralHi := (1458604452691509651/781250000000000000)
  directionLo := (96627138960558244641/50000000000000000000)
  directionHi := (193254277921116489283/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree016.table
  base := (-2807415362374007538869897522803396590597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-46858744017753173337625939130700000000000000)
      constant := (97124674879196147594767414513854593862742454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree016.table
  base := (-2842595804485848543334442662992122724439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-67942413399971372993308983666282800000000000000)
      constant := (141542142815970876680205073118971157804150751112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96627138960558244641/50000000000000000000)
  centralHi := (193254277921116489283/100000000000000000000)
  directionLo := (24949019999060795503/12500000000000000000)
  directionHi := (7983686399699454561/4000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree017.table
  base := (-7155202544474138991287816590814857282881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-50888030098929091273873838047900000000000000)
      constant := (116598898109921244353282335962289980262115871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree017.table
  base := (-3609558871104456236306164269533225917091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-73778101691085385411612020175316600000000000000)
      constant := (169917051053804537057760890746542713205133593128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/12500000000000000000)
  centralHi := (7983686399699454561/4000000000000000000)
  directionLo := (205734889423550172131/100000000000000000000)
  directionHi := (51433722355887543033/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree018.table
  base := (-529060199191824872070061624246249844131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-54917316180105009210121736965100000000000000)
      constant := (138468590234883548581570552533040545509033936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree018.table
  base := (-1704585696375524725904309889892496703117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-79613789982199397829915056684350400000000000000)
      constant := (201765747884767943781278695474965467931921029340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205734889423550172131/100000000000000000000)
  centralHi := (51433722355887543033/25000000000000000000)
  directionLo := (211699454703536160581/100000000000000000000)
  directionHi := (105849727351768080291/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree019.table
  base := (-9571145881095483289558740064673924757211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-58946602261280927146369635882300000000000000)
      constant := (162674034852188958739792428273735300211320901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree019.table
  base := (-9623614923919093888687443602540669390149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (8995565)
      previous := (7960719)
      next := (0)
      square := (327104770044554065188124884823600000000000000)
      linear := (-4497340961753337381485162799651800000000000000)
      constant := (12473796695736423096929479676695037260104225284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211699454703536160581/100000000000000000000)
  centralHi := (105849727351768080291/50000000000000000000)
  directionLo := (217500513832562475557/100000000000000000000)
  directionHi := (108750256916281237779/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree020.table
  base := (-10496256174291783324215891298496078028131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-62975888342456845082617534799500000000000000)
      constant := (189165517206882491421082842421622163635858621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree020.table
  base := (-2635913654518088593091579153682646092097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-91285166564427422666521129702418000000000000000)
      constant := (275554520258229459721256471263198840904053431152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217500513832562475557/100000000000000000000)
  centralHi := (108750256916281237779/50000000000000000000)
  directionLo := (1785206550076853697/800000000000000000)
  directionHi := (111575409379803356063/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree021.table
  base := (-5629618052434952625113745662880756344111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-67005174423632763018865433716700000000000000)
      constant := (217901194336554264535806465911992818471717602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree021.table
  base := (-141274597774221402501205346092442188527/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-97120854855541435084824166211451800000000000000)
      constant := (317362545240467777171393106645473507144426360640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1785206550076853697/800000000000000000)
  centralHi := (111575409379803356063/50000000000000000000)
  directionLo := (228661545321326351481/100000000000000000000)
  directionHi := (114330772660663175741/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree022.table
  base := (-5938072767831238199495904743514116628141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-71034460504808680955113332633900000000000000)
      constant := (248845590004207004308904521771554632736873062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree022.table
  base := (-11914594715611618049360053058198531858431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-102956543146655447503127202720485600000000000000)
      constant := (362375047263396053206839765190235655872104229924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228661545321326351481/100000000000000000000)
  centralHi := (114330772660663175741/50000000000000000000)
  directionLo := (117021276595744680851/50000000000000000000)
  directionHi := (234042553191489361703/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree023.table
  base := (-12360666592931591055352656731293904127877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-75063746585984598891361231551100000000000000)
      constant := (281968480392927744465157031613971765781519707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree023.table
  base := (-6197598954132130429796725613196819655469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-108792231437769459921430239229519400000000000000)
      constant := (410548445390933655829338427281600199900527211352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117021276595744680851/50000000000000000000)
  centralHi := (234042553191489361703/100000000000000000000)
  directionLo := (29912824146813809891/12500000000000000000)
  directionHi := (239302593174510479129/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree024.table
  base := (-12724492520691965465570739337747253201113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-79093032667160516827609130468300000000000000)
      constant := (317244035126687976816574095268516317678741383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree024.table
  base := (-12755450569309396057356530120172521598601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-114627919728883472339733275738553200000000000000)
      constant := (461845504593977265634270004849852571294868924604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29912824146813809891/12500000000000000000)
  centralHi := (239302593174510479129/100000000000000000000)
  directionLo := (122224737160383588507/50000000000000000000)
  directionHi := (48889894864153435403/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree025.table
  base := (-3244409317569253890759303555360261431989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-83122318748336434763857029385500000000000000)
      constant := (354650133386992185566294647109836729986945196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree025.table
  base := (-812834120280732579525993833170897023033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-120463608019997484758036312247587000000000000000)
      constant := (516234348521019349100995479307832010752278859712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122224737160383588507/50000000000000000000)
  centralHi := (48889894864153435403/20000000000000000000)
  directionLo := (24949019999060795503/10000000000000000000)
  directionHi := (249490199990607955031/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree026.table
  base := (-13128688023614940541442236746763434717049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-87151604829512352700104928302700000000000000)
      constant := (394167806088960978695457133937999572710038759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree026.table
  base := (-13153449981678350806455351616070265361127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-126299296311111497176339348756620800000000000000)
      constant := (573687653354429416498461114390045431832138539908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/10000000000000000000)
  centralHi := (249490199990607955031/100000000000000000000)
  directionLo := (50886215928091055409/20000000000000000000)
  directionHi := (127215539820227638523/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree027.table
  base := (-6592507381321710677197054470246656449983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-91180890910688270636352827219900000000000000)
      constant := (435780772942494018977540816575850271803975106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree027.table
  base := (-13207111413349713030544816417867570314909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-132134984602225509594642385265654600000000000000)
      constant := (634181978328124087330341514304340420679784531436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50886215928091055409/20000000000000000000)
  centralHi := (127215539820227638523/50000000000000000000)
  directionLo := (259277821424551926397/100000000000000000000)
  directionHi := (129638910712275963199/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree028.table
  base := (-328823656953649751590087141761037412887/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-95210176991864188572600726137100000000000000)
      constant := (479475053648750484088226858420394734197304680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree028.table
  base := (-13172637891213428188420218698285117546061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-137970672893339522012945421774688400000000000000)
      constant := (697697203256121081373648806929714525192044806444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259277821424551926397/100000000000000000000)
  centralHi := (129638910712275963199/50000000000000000000)
  directionLo := (264035609489167161619/100000000000000000000)
  directionHi := (13201780474458358081/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree029.table
  base := (-13037919183846534597194552174615933098479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-99239463073040106508848625054300000000000000)
      constant := (525238638728014305594288934280873403785459889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree029.table
  base := (-3263861347859687924948090112288520714719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-143806361184453534431248458283722200000000000000)
      constant := (764216052279299612367611154915832628113088770704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264035609489167161619/100000000000000000000)
  centralHi := (13201780474458358081/5000000000000000000)
  directionLo := (268709168942874225523/100000000000000000000)
  directionHi := (67177292235718556381/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree030.table
  base := (-200696949191439066342637422811961047479/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-103268749154216024445096523971500000000000000)
      constant := (573061209348153420448434920242536194951608896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree030.table
  base := (-6430092631973217001799261486876370105573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-149642049475567546849551494792756000000000000000)
      constant := (833723688540287870245108174110622904285447333784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268709168942874225523/100000000000000000000)
  centralHi := (67177292235718556381/25000000000000000000)
  directionLo := (34162852602832789947/12500000000000000000)
  directionHi := (273302820822662319577/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree031.table
  base := (-12577017222664723926126507288479934378697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-107298035235391942381344422888700000000000000)
      constant := (622933898028041629102513289152347824957458327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree031.table
  base := (-3147713185072686671168026629964581085831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-155477737766681559267854531301789800000000000000)
      constant := (906207368065454965721924623737326521442962478096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34162852602832789947/12500000000000000000)
  centralHi := (273302820822662319577/100000000000000000000)
  directionLo := (55564105775321681683/20000000000000000000)
  directionHi := (8681891527394012763/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree032.table
  base := (-12238606574567656121286841595094545808037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-111327321316567860317592321805900000000000000)
      constant := (674849083789508431238474412618836148310046267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree032.table
  base := (-245017595860925908791265115771087398381/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-161313426057795571686157567810823600000000000000)
      constant := (981656143562410311845627638429006025049693986200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55564105775321681683/20000000000000000000)
  centralHi := (8681891527394012763/3125000000000000000)
  directionLo := (11290637584188595231/4000000000000000000)
  directionHi := (35283242450589360097/12500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree033.table
  base := (-11832337987726895532558829828317728437847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-115356607397743778253840220723100000000000000)
      constant := (728800216541614735725480079288646137880795977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree033.table
  base := (-1480401839383075535879974147244720037673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-167149114348909584104460604319857400000000000000)
      constant := (1060060610578409288707247693371437773021686522336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11290637584188595231/4000000000000000000)
  centralHi := (35283242450589360097/12500000000000000000)
  directionLo := (35830302088583722181/12500000000000000000)
  directionHi := (286642416708669777449/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree034.table
  base := (-2840190020475846887710753090507100252921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-119385893478919696190088119640300000000000000)
      constant := (784781666383308614195030995475879262165190044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree034.table
  base := (-11370390379508495221559063263184794843807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-172984802640023596522763640828891200000000000000)
      constant := (1141412689764768619360152728668294094146403806628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35830302088583722181/12500000000000000000)
  centralHi := (286642416708669777449/100000000000000000000)
  directionLo := (1136535433109819079/390625000000000000)
  directionHi := (11638122835044547369/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree035.table
  base := (-10826063488438367759512966049325549853643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-123415179560095614126336018557500000000000000)
      constant := (842788594209957277243454929912039860373302613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree035.table
  base := (-10834582824727024313250370099197895503857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-178820490931137608941066677337925000000000000000)
      constant := (1225705440003066638148068570762272074713378956828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1136535433109819079/390625000000000000)
  centralHi := (11638122835044547369/4000000000000000000)
  directionLo := (147600392824591573901/50000000000000000000)
  directionHi := (295200785649183147803/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree036.table
  base := (-10230131164808982365168613060946659838521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-127444465641271532062583917474700000000000000)
      constant := (902816840568493708900372654521968828416707111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree036.table
  base := (-1023766155409457337830990902279095012103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-184656179222251621359369713846958800000000000000)
      constant := (1312932897958917755451219860552847918467738990120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147600392824591573901/50000000000000000000)
  centralHi := (295200785649183147803/100000000000000000000)
  directionLo := (74847059997182386509/25000000000000000000)
  directionHi := (299388239988729546037/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree037.table
  base := (-1914916324824062560775141992465191862249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-131473751722447449998831816391900000000000000)
      constant := (964862830163468784273514913052621955881459795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree037.table
  base := (-4790616366412187214961388319828207338211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-190491867513365633777672750355992600000000000000)
      constant := (1403089940292949464646876829627570252090807810088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74847059997182386509/25000000000000000000)
  centralHi := (299388239988729546037/100000000000000000000)
  directionLo := (2428143424287166897/800000000000000000)
  directionHi := (151758964017947931063/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree038.table
  base := (-4430403041619756466968591239699041381713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-135503037803623367935079715309100000000000000)
      constant := (1028923489796822960489890542575409635175591966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree038.table
  base := (-4433338145251085679863230223299124547139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (8995565)
      previous := (7960719)
      next := (0)
      square := (327104770044554065188124884823600000000000000)
      linear := (-10333029252867349799788199308685600000000000000)
      constant := (78745903437436256748024725627320199549056232248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2428143424287166897/800000000000000000)
  centralHi := (151758964017947931063/50000000000000000000)
  directionLo := (307592176485126814967/100000000000000000000)
  directionHi := (38449022060640851871/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree039.table
  base := (-4045000194199471148215535664050052827731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-139532323884799285871327614226300000000000000)
      constant := (1094996177844228955323258151148826866607084442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree039.table
  base := (-8095177792272771884279607938733448656241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-202163244095593658614278823374060200000000000000)
      constant := (1592175791302979349072950824882054325410117083164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307592176485126814967/100000000000000000000)
  centralHi := (38449022060640851871/12500000000000000000)
  directionLo := (311613159912272549203/100000000000000000000)
  directionHi := (77903289978068137301/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree040.table
  base := (-7263192454322666659734210215892821301151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-143561609965975203807575513143500000000000000)
      constant := (1163078623642061307491273313113092757745757441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree040.table
  base := (-90846947725182936738641125663778521529/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-207998932386707671032581859883094000000000000000)
      constant := (1691097569205998888429668851077794554171270553280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311613159912272549203/100000000000000000000)
  centralHi := (77903289978068137301/25000000000000000000)
  directionLo := (315582914344496295689/100000000000000000000)
  directionHi := (31558291434449629569/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree041.table
  base := (-398829115523187453665749031201363234743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-147590896047151121743823412060700000000000000)
      constant := (1233168875390021085058250932215819017831243408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree041.table
  base := (-6385285483572362513259709206769656866813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-213834620677821683450884896392127800000000000000)
      constant := (1792934707579326848236206375829160500604867359852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315582914344496295689/100000000000000000000)
  centralHi := (31558291434449629569/10000000000000000000)
  directionLo := (63900669862473218983/20000000000000000000)
  directionHi := (79875837328091523729/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree042.table
  base := (-2722490030928880672728038301590451987661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-151620182128327039680071310977900000000000000)
      constant := (1305265255371796056877922861979973383118513702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree042.table
  base := (-5448518648186813004265263194785672347429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-219670308968935695869187932901161600000000000000)
      constant := (1897684808145364175339714016171092541488860365516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63900669862473218983/20000000000000000000)
  centralHi := (79875837328091523729/25000000000000000000)
  directionLo := (323376258586609864503/100000000000000000000)
  directionHi := (40422032323326233063/12500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree043.table
  base := (-2227493967098492249751038017339346686343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-155649468209502957616319209895100000000000000)
      constant := (1379366321465120627191492605184794766339736626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree043.table
  base := (-4458101275279016370709756842889995708609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-225505997260049708287490969410195400000000000000)
      constant := (2005345810412574322062363569477665588248661846236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323376258586609864503/100000000000000000000)
  centralHi := (40422032323326233063/12500000000000000000)
  directionLo := (327203329770844649129/100000000000000000000)
  directionHi := (32720332977084464913/10000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree044.table
  base := (-106620332185742957864890387808232931797/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-159678754290678875552567108812300000000000000)
      constant := (1455470834057492566997631862088211630517133664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree044.table
  base := (-853647086939440515979520171213403877903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-231341685551163720705794005919229200000000000000)
      constant := (2115915944098694763447476705223819076655522088848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327203329770844649129/100000000000000000000)
  centralHi := (32720332977084464913/10000000000000000000)
  directionLo := (165493076447915378051/50000000000000000000)
  directionHi := (330986152895830756103/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree045.table
  base := (-2316050512503245062249227047288280923853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-163708040371854793488815007729500000000000000)
      constant := (1533577727608149981104404420677540187439208723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree045.table
  base := (-2318456682413382007158053703753474223681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-237177373842277733124097042428263000000000000000)
      constant := (2229393688255434965887541427488610107935199240924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165493076447915378051/50000000000000000000)
  centralHi := (330986152895830756103/100000000000000000000)
  directionLo := (83681557034852517047/25000000000000000000)
  directionHi := (334726228139410068189/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree046.table
  base := (-1168002209945206143660477775944780465837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-167737326453030711425062906646700000000000000)
      constant := (1613686086203686658310729883948537979950966067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree046.table
  base := (-585057969686335176213056278986214807119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-243013062133391745542400078937296800000000000000)
      constant := (2345777736150561121903696110604875675906222084552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83681557034852517047/25000000000000000000)
  centralHi := (334726228139410068189/100000000000000000000)
  directionLo := (338424972778443964973/100000000000000000000)
  directionHi := (169212486389221982487/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree047.table
  base := (6387574631741136302246629343466181311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2525)
      previous := (2222)
      next := (0)
      square := (91574683663089044005634066300000000000000)
      linear := (-3654608777323545305559804373700000000000000)
      constant := (36080747288221358590619836090095714552608085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree047.table
  base := (7520479782132358913944756892171295059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 678680000000000000000000000000000000000000000
      center := (3636505)
      previous := (3218163)
      next := (0)
      square := (132233843209500579544135591737200000000000000)
      linear := (-5294654264351186339589427988219800000000000000)
      constant := (52448233299922152913954541982355706525812256848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338424972778443964973/100000000000000000000)
  centralHi := (169212486389221982487/50000000000000000000)
  directionLo := (171041863732058796263/50000000000000000000)
  directionHi := (342083727464117592527/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree048.table
  base := (641731689816972665953661905111849087973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-175795898615382547297558704481100000000000000)
      constant := (1779904159893302997364890550095184149270664714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree048.table
  base := (320458625556717907308729456833919479369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-254684438715619770379006151955364400000000000000)
      constant := (2587260410527608824294721873848141636078453274896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171041863732058796263/50000000000000000000)
  centralHi := (342083727464117592527/100000000000000000000)
  directionLo := (34570376189940256853/10000000000000000000)
  directionHi := (345703761899402568531/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree049.table
  base := (258631097175356097294936175581286674701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-179825184696558465233806603398300000000000000)
      constant := (1866012616531345252525420888229190622644145090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree049.table
  base := (2584882008513225795800276832851316834491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-260520127006733782797309188464398200000000000000)
      constant := (2712357243730868395303169368729613324033392053836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34570376189940256853/10000000000000000000)
  centralHi := (345703761899402568531/100000000000000000000)
  directionLo := (174643139993425568521/50000000000000000000)
  directionHi := (349286279986851137043/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree050.table
  base := (985063572550798864783923317777644674531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-183854470777734383170054502315500000000000000)
      constant := (1954119992432805204306310157585883268344155916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree050.table
  base := (3939001227496107314903940627307552674267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-266355815297847795215612224973432000000000000000)
      constant := (2840356752710187004304839679010260622290166179532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174643139993425568521/50000000000000000000)
  centralHi := (349286279986851137043/100000000000000000000)
  directionLo := (352832424505893600969/100000000000000000000)
  directionHi := (35283242450589360097/10000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree051.table
  base := (5345098761368471409156578751075387575277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-187883756858910301106302401232700000000000000)
      constant := (2044225857784568693072245143377725531153786893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree051.table
  base := (267200019296908556013905732156850718499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-272191503588961807633915261482465800000000000000)
      constant := (2971258325748059260956732058649635400889304724080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352832424505893600969/100000000000000000000)
  centralHi := (35283242450589360097/10000000000000000000)
  directionLo := (89085820342788436881/25000000000000000000)
  directionHi := (14253731254846149901/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree052.table
  base := (1360135426763253400938939894742045370639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-191913042940086219042550300149900000000000000)
      constant := (2136329843128219952726562888547825891118707755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree052.table
  base := (6799714720067045085367202303124399977379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-278027191880075820052218297991499600000000000000)
      constant := (3105061437281663107739047971908122598550243624684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89085820342788436881/25000000000000000000)
  centralHi := (14253731254846149901/4000000000000000000)
  directionLo := (359819883516760912727/100000000000000000000)
  directionHi := (44977485439595114091/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree053.table
  base := (830684564157104299867747631324624669729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-195942329021262136978798199067100000000000000)
      constant := (2230431630884719017072480065807360958954313610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree053.table
  base := (8306002671423101437783999105804389135639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-283862880171189832470521334500533400000000000000)
      constant := (3241765635768390257821937803415766142247304739644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359819883516760912727/100000000000000000000)
  centralHi := (44977485439595114091/12500000000000000000)
  directionLo := (181631607223019924009/50000000000000000000)
  directionHi := (363263214446039848019/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree054.table
  base := (9863480706167334411154086541523639862163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-199971615102438054915046097984300000000000000)
      constant := (2326530948069235673969285307749825720455518067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree054.table
  base := (2465685654626733712798492415803473102741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-289698568462303844888824371009567200000000000000)
      constant := (3381370533260468394093080957530182921156923323344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181631607223019924009/50000000000000000000)
  centralHi := (363263214446039848019/100000000000000000000)
  directionLo := (183337105740575382761/50000000000000000000)
  directionHi := (366674211481150765523/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree055.table
  base := (716904756363745249264492685393742298877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-204000901183613972851293996901500000000000000)
      constant := (2424627560029010378503129756727556427811508688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree055.table
  base := (11469830068761070188150790413139657923143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-295534256753417857307127407518601000000000000000)
      constant := (3523875796447955652588951701137919353284609848828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183337105740575382761/50000000000000000000)
  centralHi := (366674211481150765523/100000000000000000000)
  directionLo := (370053768743108219701/100000000000000000000)
  directionHi := (185026884371554109851/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree056.table
  base := (2625548103735554280049401907748911607443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-208030187264789890787541895818700000000000000)
      constant := (2524721265060582182585785954728686728704207935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree056.table
  base := (3281793811512388100763765527262454224281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-301369945044531869725430444027634800000000000000)
      constant := (3669281138963292668448917252919985069739178546704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370053768743108219701/100000000000000000000)
  centralHi := (185026884371554109851/50000000000000000000)
  directionLo := (74680547977805294131/20000000000000000000)
  directionHi := (1458604452691509651/390625000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree057.table
  base := (14835195468260298118850998811881849699993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-212059473345965808723789794735900000000000000)
      constant := (2626811889782897488248132137162847005987284537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree057.table
  base := (14834701017931070421996708669587832327049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (8995565)
      previous := (7960719)
      next := (0)
      square := (327104770044554065188124884823600000000000000)
      linear := (-16168717543981362218091235817719400000000000000)
      constant := (200925595514196140914455976201703858642394294316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74680547977805294131/20000000000000000000)
  centralHi := (1458604452691509651/390625000000000000)
  directionLo := (94180485157583900579/25000000000000000000)
  directionHi := (376721940630335602317/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree058.table
  base := (3318554696604934871672248097513155897599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-216088759427141726660037693653100000000000000)
      constant := (2730899285160154184493595417881432806888980955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree058.table
  base := (8296170557433514674821149823676593878087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-313041321626759894562036517045702400000000000000)
      constant := (3968791112480948547523435590767687708891892800504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94180485157583900579/25000000000000000000)
  centralHi := (376721940630335602317/100000000000000000000)
  directionLo := (47501518881626999187/12500000000000000000)
  directionHi := (380012151053015993497/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree059.table
  base := (4600104142190107977492137599637044530569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-220118045508317644596285592570300000000000000)
      constant := (2836983323083141347048916309058992925472107684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree059.table
  base := (4600009650061671955812155099736611556541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-318877009917873906980339553554736200000000000000)
      constant := (4122895350480785082539320526629271303386433022544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47501518881626999187/12500000000000000000)
  centralHi := (380012151053015993497/100000000000000000000)
  directionLo := (383274117758549392241/100000000000000000000)
  directionHi := (191637058879274696121/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree060.table
  base := (20258074874307845543793024876106659572489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-224147331589493562532533491487500000000000000)
      constant := (2945063893430647142881290103491319610995628201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree060.table
  base := (2532218069487846400967407229804499489709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-324712698208987919398642590063770000000000000000)
      constant := (4279898872730261982460450153261271786034206474912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383274117758549392241/100000000000000000000)
  centralHi := (191637058879274696121/50000000000000000000)
  directionLo := (96627138960558244641/25000000000000000000)
  directionHi := (77301711168446595713/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree061.table
  base := (22165705548082152587393545085281399648613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-228176617670669480468781390404700000000000000)
      constant := (3055140901543520831247294369671986611823786117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree061.table
  base := (22165416952766581260315267866726335968049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-330548386500101931816945626572803800000000000000)
      constant := (4439801545165224029906737369972170724565538828004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96627138960558244641/25000000000000000000)
  centralHi := (77301711168446595713/20000000000000000000)
  directionLo := (389716150723706433987/100000000000000000000)
  directionHi := (97429037680926608497/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree062.table
  base := (6030817938792798408397515621726845972847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-232205903751845398405029289321900000000000000)
      constant := (3167214266053441452016468380377978411016076092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree062.table
  base := (2412301968058643684905267110078241323911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-336384074791215944235248663081837600000000000000)
      constant := (4602603252601334853410295595021880438620460121560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389716150723706433987/100000000000000000000)
  centralHi := (97429037680926608497/25000000000000000000)
  directionLo := (392897559842965699523/100000000000000000000)
  directionHi := (98224389960741424881/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree063.table
  base := (5226148366491554492830019622858620932171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-236235189833021316341277188239100000000000000)
      constant := (3281283917016583118742736589571873468195828695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree063.table
  base := (26130521714306003615011733642308795999073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-342219763082329956653551699590871400000000000000)
      constant := (4768303896074993857858316300980553753242659059108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392897559842965699523/100000000000000000000)
  centralHi := (98224389960741424881/25000000000000000000)
  directionLo := (396053414233750742429/100000000000000000000)
  directionHi := (39605341423375074243/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree064.table
  base := (704702214059611472010895561525031321171/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-240264475914197234277525087156300000000000000)
      constant := (3397349794309361468117308031873951767538669560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree064.table
  base := (28187896397854505613212933356004130114033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-348055451373443969071854736099905200000000000000)
      constant := (4936903390558773106424607588059094950221222007268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396053414233750742429/100000000000000000000)
  centralHi := (39605341423375074243/10000000000000000000)
  directionLo := (24949019999060795503/6250000000000000000)
  directionHi := (399184319984972728049/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree065.table
  base := (1211811541948013413289062960849025105899/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-244293761995373152213772986073500000000000000)
      constant := (3515411846249458223271745266017887411473272275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree065.table
  base := (30295120828811817059271271649231164414789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-353891139664557981490157772608939000000000000000)
      constant := (5108401662998624491562641325286704096325636293044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24949019999060795503/6250000000000000000)
  centralHi := (399184319984972728049/100000000000000000000)
  directionLo := (402290859599766745029/100000000000000000000)
  directionHi := (40229085959976674503/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree066.table
  base := (6490464335973751457177237505724567368569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-248323048076549070150020884990700000000000000)
      constant := (3635470028410488936431246002930327846585844605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree066.table
  base := (2028260958108787721090980295569669377707/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-359726827955671993908460809117972800000000000000)
      constant := (5282798650627537113702456228301123085637316444352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402290859599766745029/100000000000000000000)
  centralHi := (40229085959976674503/10000000000000000000)
  directionLo := (405373593260801068697/100000000000000000000)
  directionHi := (202686796630400534349/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree067.table
  base := (34659170667826230115521993043967008648883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-252352334157724988086268783907900000000000000)
      constant := (3757524302603121347967213334715523122105382547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree067.table
  base := (34659042993978799101887357956426207134831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-365562516246786006326763845627006600000000000000)
      constant := (5460094299516707941538151837681399214813855384476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405373593260801068697/100000000000000000000)
  centralHi := (202686796630400534349/50000000000000000000)
  directionLo := (408433060009626943233/100000000000000000000)
  directionHi := (204216530004813471617/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree068.table
  base := (18457910325755568456511601902600713532999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-256381620238900906022516682825100000000000000)
      constant := (3881574635999270346129630533416089952388789582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree068.table
  base := (4614463661925621707478275060619949064523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-371398204537900018745066882136040400000000000000)
      constant := (5640288563330772941845626182606667768369753658464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408433060009626943233/100000000000000000000)
  centralHi := (204216530004813471617/50000000000000000000)
  directionLo := (205734889423550172131/50000000000000000000)
  directionHi := (411469778847100344263/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree069.table
  base := (39222258856066938415983854953676315421977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-260410906320076823958764581742300000000000000)
      constant := (4007621000379277835687842822659270980767147193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree069.table
  base := (39222161753166261106163215983883404346297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-377233892829014031163369918645074200000000000000)
      constant := (5823381402258357565734267007016827872650200785412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205734889423550172131/50000000000000000000)
  centralHi := (411469778847100344263/100000000000000000000)
  directionLo := (414484249761237378743/100000000000000000000)
  directionHi := (51810531220154672343/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree070.table
  base := (41578474299901695879937022237572875847113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-264440192401252741895012480659500000000000000)
      constant := (4135663371484807223955322766772798482746272617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree070.table
  base := (2598649352726724308460226820861465719039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-383069581120128043581672955154108000000000000000)
      constant := (6009372782093253553466209506737113418475643616704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414484249761237378743/100000000000000000000)
  centralHi := (51810531220154672343/12500000000000000000)
  directionLo := (104369238672066933343/25000000000000000000)
  directionHi := (417476954688267733373/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree071.table
  base := (1099611438572091025638242933298029666177/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-268469478482428659831260379576700000000000000)
      constant := (4265701728462607434802979614546813901303399720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree071.table
  base := (2199219187644563842838064142638669199013/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-388905269411242055999975991663141800000000000000)
      constant := (6198262673445006940041007936572351654126697426960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104369238672066933343/25000000000000000000)
  centralHi := (417476954688267733373/100000000000000000000)
  directionLo := (420448358412117114487/100000000000000000000)
  directionHi := (52556044801514639311/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree072.table
  base := (46440200469896220433133085108077815476737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-272498764563604577767508278493900000000000000)
      constant := (4397736053386386001726853225002143894388112033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree072.table
  base := (46440136164172830538645972138270929174137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-394740957702356068418279028172175600000000000000)
      constant := (6390051051060690212577350411446125656795945506052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420448358412117114487/100000000000000000000)
  centralHi := (52556044801514639311/12500000000000000000)
  directionLo := (423398909407072321163/100000000000000000000)
  directionHi := (105849727351768080291/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree073.table
  base := (24472848052393612200573894536645206050089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-276528050644780495703756177411100000000000000)
      constant := (4531766330845822693496110663826298520329293202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree073.table
  base := (6118205009390447055066324247508404476369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-400576645993470080836582064681209400000000000000)
      constant := (6584737893242198781610485332124883273520831445792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423398909407072321163/100000000000000000000)
  centralHi := (105849727351768080291/25000000000000000000)
  directionLo := (85265808125590969887/20000000000000000000)
  directionHi := (106582260156988712359/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree074.table
  base := (51500938450443881654432497107508041857327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-280557336725956413640004076328300000000000000)
      constant := (4667792547593295398363964728366085264462835343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree074.table
  base := (12875222410220561946560378420883831938743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-406412334284584093254885101190243200000000000000)
      constant := (6782323181345617557822841143354242154331498665712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85265808125590969887/20000000000000000000)
  centralHi := (106582260156988712359/25000000000000000000)
  directionLo := (42923917025174498721/10000000000000000000)
  directionHi := (429239170251744987211/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree075.table
  base := (54105922351325157483821457830919633859793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-284586622807132331576251975245500000000000000)
      constant := (4805814692240213970657868273823501471196282737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree075.table
  base := (6763234979903963221394882729628800215489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-412248022575698105673188137699277000000000000000)
      constant := (6982806899351098400723997242123615352297327601952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42923917025174498721/10000000000000000000)
  centralHi := (429239170251744987211/100000000000000000000)
  directionLo := (216064851187126605331/50000000000000000000)
  directionHi := (432129702374253210663/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree076.table
  base := (56760643375297683751607374256134398993607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-288615908888308249512499874162700000000000000)
      constant := (4945832754995995800161625881153400887376877863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree076.table
  base := (28380303177373690538079396200298239751459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (8995565)
      previous := (7960719)
      next := (0)
      square := (327104770044554065188124884823600000000000000)
      linear := (-22004405835095374636394272326753200000000000000)
      constant := (378220475447016698989373039313291339364867885512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216064851187126605331/50000000000000000000)
  centralHi := (432129702374253210663/100000000000000000000)
  directionLo := (217500513832562475557/50000000000000000000)
  directionHi := (87000205533024990223/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree077.table
  base := (29732548856032296857837685864407903000691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-292645194969484167448747773079900000000000000)
      constant := (5087846727443695108241905792244354115457052838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree077.table
  base := (59465065479262533691226763654261173738129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-423919399157926130509794210717344600000000000000)
      constant := (7392469571943978763428130226598401399945188931684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217500513832562475557/50000000000000000000)
  centralHi := (87000205533024990223/20000000000000000000)
  directionLo := (437853523984184630227/100000000000000000000)
  directionHi := (109463380996046157557/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree078.table
  base := (62219282085857192118507427298339960442177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-296674481050660085384995671997100000000000000)
      constant := (5231856602347138847074850694398432972616768993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree078.table
  base := (3888703376647011192362345698988581630879/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-429755087449040142928097247226378400000000000000)
      constant := (7601648504539037178632946780730552807709620970944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437853523984184630227/100000000000000000000)
  centralHi := (109463380996046157557/25000000000000000000)
  directionLo := (110171889240467974107/25000000000000000000)
  directionHi := (440687556961871896429/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree079.table
  base := (32511596840193297069408869716913848192261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-300703767131836003321243570914300000000000000)
      constant := (5377862373485144870090240252033925381313409098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree079.table
  base := (16255792314465303720415136550803652041089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-435590775740154155346400283735412200000000000000)
      constant := (7813725822544336333543486017673441669264230111376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110171889240467974107/25000000000000000000)
  centralHi := (440687556961871896429/100000000000000000000)
  directionLo := (443503480546294280731/100000000000000000000)
  directionHi := (110875870136573570183/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree080.table
  base := (16969207518583430500265634243021342676051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-304733053213011921257491469831500000000000000)
      constant := (5525864035509019334481898274651336583885586636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree080.table
  base := (67876808820780378582825536177149897958797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-441426464031268167764703320244446000000000000000)
      constant := (8028701518454256694610533046055048035909378835412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443503480546294280731/100000000000000000000)
  centralHi := (110875870136573570183/25000000000000000000)
  directionLo := (446301637519213424251/100000000000000000000)
  directionHi := (111575409379803356063/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree081.table
  base := (70780189185897807578170931743388018930061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-308762339294187839193739368748700000000000000)
      constant := (5675861583820064343457125170283744133816504749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree081.table
  base := (70780170693012593811591602509726453782497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-447262152322382180183006356753479800000000000000)
      constant := (8246575585818721096018321418337774928369593800612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446301637519213424251/100000000000000000000)
  centralHi := (111575409379803356063/25000000000000000000)
  directionLo := (224541179991547159527/50000000000000000000)
  directionHi := (89816471996618863811/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree082.table
  base := (4608329326570709964523632834111628571687/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-312791625375363757129987267665900000000000000)
      constant := (5827855014464285888429898499261241400237705328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree082.table
  base := (18433313284194384587887876807376611196093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-453097840613496192601309393262513600000000000000)
      constant := (8467348019094564817082244192469281839547410668112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224541179991547159527/50000000000000000000)
  centralHi := (89816471996618863811/20000000000000000000)
  directionLo := (451845969821176623441/100000000000000000000)
  directionHi := (225922984910588311721/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree083.table
  base := (122777709844749089296679438271232835531/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-316820911456539675066235166583100000000000000)
      constant := (5981844324041886740772268094872620833554986875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree083.table
  base := (15347210931715725970939494719800810039381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-458933528904610205019612429771547400000000000000)
      constant := (8691018813517838433414955554243443448301886781380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451845969821176623441/100000000000000000000)
  centralHi := (225922984910588311721/50000000000000000000)
  directionLo := (454592779132372271009/100000000000000000000)
  directionHi := (45459277913237227101/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree084.table
  base := (7978858614600456906899534518646206423643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-320850197537715593002483065500300000000000000)
      constant := (6137829509629468121345150774690494699898273870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree084.table
  base := (79788573974808148198786301548015411030629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-464769217195724217437915466280581200000000000000)
      constant := (8917587964994095173801404633049123766043856261684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454592779132372271009/100000000000000000000)
  centralHi := (45459277913237227101/10000000000000000000)
  directionLo := (228661545321326351481/50000000000000000000)
  directionHi := (457323090642652702963/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree085.table
  base := (16578164113245161864945686535386868293849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-324879483618891510938730964417500000000000000)
      constant := (6295810568713155524971200363448347960305562205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree085.table
  base := (16578161996439278971773867313960094113473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-470604905486838229856218502789615000000000000000)
      constant := (9147055470004129766965504310535341386813898607540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228661545321326351481/50000000000000000000)
  centralHi := (457323090642652702963/100000000000000000000)
  directionLo := (11500929952361517687/2500000000000000000)
  directionHi := (460037198094460707481/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree086.table
  base := (1720855418699670472482562481562875642171/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-328908769700067428874978863334700000000000000)
      constant := (6455787499131114684751144666972219614677786950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree086.table
  base := (17208552346484527102091917492878068003049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-476440593777952242274521539298648800000000000000)
      constant := (9379421325522992527841943280120400349019268440020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11500929952361517687/2500000000000000000)
  centralHi := (460037198094460707481/100000000000000000000)
  directionLo := (231367693307782398641/50000000000000000000)
  directionHi := (462735386615564797283/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree087.table
  base := (89244436410626954250248712108622628815369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-332938055781243346811226762251900000000000000)
      constant := (6617760299024139076888250617877347387053150121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree087.table
  base := (44622214205150832416781216976630344978563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-482276282069066254692824575807682600000000000000)
      constant := (9614685528950408949241823982018344860782480686296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231367693307782398641/50000000000000000000)
  centralHi := (462735386615564797283/100000000000000000000)
  directionLo := (58177241633583397999/12500000000000000000)
  directionHi := (465417933068667183993/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree088.table
  base := (46247908134637541542228148444561443823767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-336967341862419264747474661169100000000000000)
      constant := (6781728966793175532358455931330472458813402606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree088.table
  base := (739966474520339127292634157133319099637/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-488111970360180267111127612316716400000000000000)
      constant := (9852848078050998409333947847945637691343213006500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58177241633583397999/12500000000000000000)
  centralHi := (465417933068667183993/100000000000000000000)
  directionLo := (117021276595744680851/25000000000000000000)
  directionHi := (93617021276595744681/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree089.table
  base := (9579690988828854122634178306452315247899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-340996627943595182683722560086300000000000000)
      constant := (6947693501062813685260756915692131643826088910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree089.table
  base := (47898451922072883489426754826064475431441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-493947658651294279529430648825750200000000000000)
      constant := (10093908970902911858741410566086451843946617552072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117021276595744680851/25000000000000000000)
  centralHi := (93617021276595744681/20000000000000000000)
  directionLo := (470737167868884824233/100000000000000000000)
  directionHi := (235368583934442412117/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree090.table
  base := (99147716732062197306108896089937786274297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-345025914024771100619970459003500000000000000)
      constant := (7115653900649901800399273600492672569879922073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree090.table
  base := (99147711479570338337475677275256151228877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-499783346942408291947733685334784000000000000000)
      constant := (10337868205853702737434639279271060470165266939092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470737167868884824233/100000000000000000000)
  centralHi := (235368583934442412117/50000000000000000000)
  directionLo := (236687185758372221767/50000000000000000000)
  directionHi := (94674874303348888707/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree091.table
  base := (102548236339812549945056686760646280145331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-349055200105947018556218357920700000000000000)
      constant := (7285610164536569123228455588938867632841036179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree091.table
  base := (102548231775846029135877711500272134958463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-505619035233522304366036721843817800000000000000)
      constant := (10584725781482412379342605592759539580001965443548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236687185758372221767/50000000000000000000)
  centralHi := (94674874303348888707/20000000000000000000)
  directionLo := (95199392856157845407/20000000000000000000)
  directionHi := (118999241070197306759/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree092.table
  base := (105998468315079810950739113288147035104807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-353084486187122936492466256837900000000000000)
      constant := (7457562291847035981631189574719916800546518663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree092.table
  base := (105998464349861776292110657007325948536833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-511454723524636316784339758352851600000000000000)
      constant := (10834481696566994647890761056668449881338995756068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95199392856157845407/20000000000000000000)
  centralHi := (118999241070197306759/25000000000000000000)
  directionLo := (29912824146813809891/6250000000000000000)
  directionHi := (478605186349020958257/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree093.table
  base := (109498412316703900888073660716819323536089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-357113772268298854428714155755100000000000000)
      constant := (7631510281827679760135378282298853885691220601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree093.table
  base := (109498408872091264795827553780104051726281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-517290411815750329202642794861885400000000000000)
      constant := (11087135950056327821564360979325594508780284228676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29912824146813809891/6250000000000000000)
  centralHi := (478605186349020958257/100000000000000000000)
  directionLo := (120299817849985546943/25000000000000000000)
  directionHi := (481199271399942187773/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree094.table
  base := (113048068051067390038453080719059444979361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2525)
      previous := (2222)
      next := (0)
      square := (91574683663089044005634066300000000000000)
      linear := (-7683894858499463241807703290900000000000000)
      constant := (166116045400636160776438687236595793914029967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree094.table
  base := (113048065059054222288144484378968293000461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 678680000000000000000000000000000000000000000
      center := (3636505)
      previous := (3218163)
      next := (0)
      square := (132233843209500579544135591737200000000000000)
      linear := (-11130342555465198757892464497253600000000000000)
      constant := (241333798745663141734343125030163520109355287148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120299817849985546943/25000000000000000000)
  centralHi := (481199271399942187773/100000000000000000000)
  directionLo := (241889723423448356353/50000000000000000000)
  directionHi := (483779446846896712707/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree095.table
  base := (116647435265427481118340409617026288941563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-365172344430650690301209953589500000000000000)
      constant := (7985393847295386531503576475419011072271912667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree095.table
  base := (58323716333419628933095325038577219716847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (8995565)
      previous := (7960719)
      next := (0)
      square := (327104770044554065188124884823600000000000000)
      linear := (-27840094126209387054697308835787000000000000000)
      constant := (610586287829394030983349741349962370909886283496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241889723423448356353/50000000000000000000)
  centralHi := (483779446846896712707/100000000000000000000)
  directionLo := (243172967035371503611/50000000000000000000)
  directionHi := (486345934070743007223/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree096.table
  base := (60148256871092056112210685628512585659373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-369201630511826608237457852506700000000000000)
      constant := (8165329421743462148423831572172368603443109914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree096.table
  base := (120296511485538739175173487094216192412487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-534797476689092366457551904388986800000000000000)
      constant := (11862488732523722077018127706243780833692581382652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243172967035371503611/50000000000000000000)
  centralHi := (486345934070743007223/100000000000000000000)
  directionLo := (488898948641534354029/100000000000000000000)
  directionHi := (48889894864153435403/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree097.table
  base := (61997651646976366211295910292750428021533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-373230916593002526173705751423900000000000000)
      constant := (8347260856760193934239947533956771390999132794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree097.table
  base := (123995301334467258947440348433778838068569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-540633164980206378875854940898020600000000000000)
      constant := (12126736331765524537156845395422724727555769121924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell030.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488898948641534354029/100000000000000000000)
  centralHi := (48889894864153435403/10000000000000000000)
  directionLo := (245719350264916961087/50000000000000000000)
  directionHi := (19657548021193356887/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree098.table
  base := (25548760751865752168044564561311833546847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (118675)
      previous := (104434)
      next := (0)
      square := (4304010132165185068264801116100000000000000)
      linear := (-377260202674178444109953650341100000000000000)
      constant := (8531188151989039169804287043808089201524925115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree098.table
  base := (127743802058053333430773014646897019154689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (170915735)
      previous := (151253661)
      next := (0)
      square := (6214990630846527238574372811648400000000000000)
      linear := (-546468853271320391294157977407054400000000000000)
      constant := (12393882265987652672512907485660748624111550353444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell030.Kernel098
