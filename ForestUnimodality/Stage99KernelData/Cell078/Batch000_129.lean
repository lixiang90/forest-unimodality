import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell078.Parameters
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch000_049
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch050_099
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch100_149
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch000_049
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch050_099
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree000.table
  base := (4991166367358720650337033971/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18122205822128822916283752400000000000)
      linear := (-452940539569421894705580920000000000)
      constant := (9982332734717441300674067942000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree000.table
  base := (4991166367358720650337033971/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18122205822128822916283752400000000000)
      linear := (-452940539569421894705580920000000000)
      constant := (9982332734717441300674067942000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree001.table
  base := (281996646434272315973332617788784710457893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-2908654932115163084620250084543536000000000000)
      constant := (865362892793693631385156607387910270798610395893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree001.table
  base := (140746733198545398030631678114302406628147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-13118695928013122226659637427745037000000000000)
      constant := (3887206231212817250730823993518552259218747971323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4998515399417790539/10000000000000000000)
  directionHi := (49985153994177905391/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree002.table
  base := (42016611885840294944708246694777022484329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-2873937028433653407155519939386013000000000000)
      constant := (259132252514974896700709315466481927427950396658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree002.table
  base := (167541031481559256124316134537265948870119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-51849861445785314712273407098144734000000000000)
      constant := (4650005449699028385544686442366735326515603517071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4998515399417790539/10000000000000000000)
  centralHi := (49985153994177905391/100000000000000000000)
  directionLo := (70689682695874076313/100000000000000000000)
  directionHi := (35344841347937038157/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree003.table
  base := (106345306136582397749431767041140016217917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-8587093181619450544001829673000516000000000000)
      constant := (332689962858033557581357807340961667614149739917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree003.table
  base := (105921656618001326837700161119836790992693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-8606925670616042774580837704533266000000000000)
      constant := (331421739080610498381388706095390939020387730693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/100000000000000000000)
  centralHi := (35344841347937038157/50000000000000000000)
  directionLo := (43288413171035266727/50000000000000000000)
  directionHi := (17315365268414106691/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree004.table
  base := (35702468309268868551247131233285375320877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-5713156153185797136846309733614503000000000000)
      constant := (115338058607084173407591687854564971019184202877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree004.table
  base := (71088934174315028864601566407762746850461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-103074800625303455230181671583454054000000000000)
      constant := (2067855266387142094387227776312932342456342488149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/50000000000000000000)
  centralHi := (17315365268414106691/20000000000000000000)
  directionLo := (99970307988355810781/100000000000000000000)
  directionHi := (49985153994177905391/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree005.table
  base := (25248274953900068136081827281250592068139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-7132765715561869001691704630728748000000000000)
      constant := (86567584012954854457458382340710758406506242139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree005.table
  base := (25132065515634178564003300245247784914901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-64343635107531262744567901913054357000000000000)
      constant := (776283908491642595612855799287279744171842428109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99970307988355810781/100000000000000000000)
  centralHi := (49985153994177905391/50000000000000000000)
  directionLo := (13971275274597115453/12500000000000000000)
  directionHi := (894161617574215389/800000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree006.table
  base := (1486359852431273176668787781307875766181/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1226400400000000000000000000000000000000000000
      center := (12264004)
      previous := (6132002)
      next := (6132002)
      square := (111125402345705586380297802284304800000000000)
      linear := (-684190022235035269322967962227439440000000000)
      constant := (5610288954862714408883113989133314246986712181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree006.table
  base := (1155784753047110217122459153744355996869/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-8572207766934533097116107559375743000000000000)
      constant := (69923171646882867739114574262566510692101613904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13971275274597115453/12500000000000000000)
  centralHi := (894161617574215389/800000000000000000)
  directionLo := (6121906100008819241/5000000000000000000)
  directionHi := (122438122000176384821/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree007.table
  base := (28080594718734791170653571139011746996981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-19943969680628025462764988849914476000000000000)
      constant := (121888667160040246217991250084896676054490742981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree007.table
  base := (13973191714600951983575862966221210964891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-89956104697290333003522034155709017000000000000)
      constant := (547395627366726679847188521266255950356100938019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6121906100008819241/5000000000000000000)
  centralHi := (122438122000176384821/100000000000000000000)
  directionLo := (132248286713861650167/100000000000000000000)
  directionHi := (16531035839232706271/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree008.table
  base := (2690874195672459881817604921529836622927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-11391594402690084596227889322071483000000000000)
      constant := (56355987127381418290699568964219576462923219708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree008.table
  base := (10709927293724776600424026452939391355071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-102762339492169868132999100277036347000000000000)
      constant := (506702684564048234153539475686904357506351369639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132248286713861650167/100000000000000000000)
  centralHi := (16531035839232706271/12500000000000000000)
  directionLo := (70689682695874076313/50000000000000000000)
  directionHi := (141379365391748152627/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree009.table
  base := (8281209723770116318771571069875715088429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-12811203965066156461073284219185728000000000000)
      constant := (54929031482911906827545339787305476211838402429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree009.table
  base := (16474373213889526795615763474751196740413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-25681905397122089613883592532969706000000000000)
      constant := (109862800696759747203015667566741527957302998413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/50000000000000000000)
  centralHi := (141379365391748152627/100000000000000000000)
  directionLo := (37488865495633429043/25000000000000000000)
  directionHi := (149955461982533716173/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree010.table
  base := (12661253298308246790233528643728487705011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-28461627054884456651837358232599946000000000000)
      constant := (111715384708463553604037714450340647032051431011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree010.table
  base := (1573416025997537237262652698600191096031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-128374809081928938391953232519691007000000000000)
      constant := (503224915374917166194690649679779787022397113116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/25000000000000000000)
  centralHi := (149955461982533716173/100000000000000000000)
  directionLo := (79033467907932513561/50000000000000000000)
  directionHi := (158066935815865027123/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree011.table
  base := (9512989689859532840590714728980949742687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-31300846179636600381528148026828436000000000000)
      constant := (117331929530467666135634313314534865642028084687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree011.table
  base := (4725022872762683624487012285957502491113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-141181043876808473521430298641018337000000000000)
      constant := (528970847141071836331671679866065514357294542017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/50000000000000000000)
  centralHi := (158066935815865027123/100000000000000000000)
  directionLo := (41445500221705668219/25000000000000000000)
  directionHi := (165782000886822672877/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree012.table
  base := (865423659508183154998990970857862697113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-17070032652194372055609468910528463000000000000)
      constant := (63056079701183219594588753332496302548844620452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree012.table
  base := (6869360807228495272058342931649001381173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-34219395260375113033534969947187926000000000000)
      constant := (126434511065202237457541684957940101883677799173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41445500221705668219/25000000000000000000)
  centralHi := (165782000886822672877/100000000000000000000)
  directionLo := (43288413171035266727/25000000000000000000)
  directionHi := (173153652684141066909/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree013.table
  base := (595457419457542272827889444636043121777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-18489642214570443920454863807642708000000000000)
      constant := (68830597886643258749167802320792397264645615108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree013.table
  base := (4717101143918967554209738555652898683529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-333587026933135087560768861767345994000000000000)
      constant := (1242819760466696789700239370455403239149387377761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/25000000000000000000)
  centralHi := (173153652684141066909/100000000000000000000)
  directionLo := (90112017868986032813/50000000000000000000)
  directionHi := (180224035737972065627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree014.table
  base := (183985071113972026151433864267766004073/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-19909251776946515785300258704756953000000000000)
      constant := (75851489810266576470910650087472735690030576584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree014.table
  base := (2903589171967657903769301571580322309013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-359199496522894157819722994010000654000000000000)
      constant := (1370194612872013269615664293286243284017805503117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90112017868986032813/50000000000000000000)
  centralHi := (180224035737972065627/100000000000000000000)
  directionLo := (46756830167837185011/25000000000000000000)
  directionHi := (37405464134269748009/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree015.table
  base := (698976905096259596228982631264335923921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-21328861339322587650145653601871198000000000000)
      constant := (84017974773830918017209953625442289582077709921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree015.table
  base := (681651154934547575082795665000316365719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-21378442561814068226593173680703073000000000000)
      constant := (84345951449944687324120059149479229977610819719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/25000000000000000000)
  centralHi := (37405464134269748009/20000000000000000000)
  directionLo := (96795834488532086743/50000000000000000000)
  directionHi := (193591668977064173487/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree016.table
  base := (9579633873140647959629815590520071449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-22748470901698659514991048498985443000000000000)
      constant := (93254015489904152775837643544423028518330821796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree016.table
  base := (11695382667059928909106135846698747959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-205212217851206149168815629247654987000000000000)
      constant := (842776263656370745825801899586440607742938755262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/50000000000000000000)
  centralHi := (193591668977064173487/100000000000000000000)
  directionLo := (199940615976711621563/100000000000000000000)
  directionHi := (49985153994177905391/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree017.table
  base := (-264623150178561802912750130985485192109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (4806462039174117057971358230290000000000000)
      linear := (-83626576000258586089399458117992000000000000)
      constant := (358134576615124147067353101799425850193831238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree017.table
  base := (-108417641896676084662349594420061596773/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 95481000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (8651631670513410704348444814522000000000000)
      linear := (-150877821900405317853489754580610600000000000)
      constant := (647445202628704571856115953551675298678517187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/100000000000000000000)
  centralHi := (49985153994177905391/25000000000000000000)
  directionLo := (103047034815379998333/50000000000000000000)
  directionHi := (206094069630759996667/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree018.table
  base := (-2037487051556593160624348184512556617017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-51175380052901606489363676586427866000000000000)
      constant := (229425073466978392560866087547356924899669260983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree018.table
  base := (-2059545302998507714990431824177478573807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-51294374986881159872837724775624366000000000000)
      constant := (230454706071011182476927757107302484515229164193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/50000000000000000000)
  centralHi := (206094069630759996667/100000000000000000000)
  directionLo := (212069048087622228939/100000000000000000000)
  directionHi := (10603452404381111447/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree019.table
  base := (-1442086892543348088119108928446988085157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-27007299588826875109527233190328178000000000000)
      constant := (126852420190211201211928216965693162458920552843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree019.table
  base := (-181442953712610047363280602551707371081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-243630922235844754557246827611636977000000000000)
      constant := (1146911995895020007478045728330552483696196370168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212069048087622228939/100000000000000000000)
  centralHi := (10603452404381111447/5000000000000000000)
  directionLo := (21788023493793995073/10000000000000000000)
  directionHi := (217880234937939950731/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree020.table
  base := (-144703083358015052826770804120285262687/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1226400400000000000000000000000000000000000000
      center := (12264004)
      previous := (6132002)
      next := (6132002)
      square := (111125402345705586380297802284304800000000000)
      linear := (-2274152732096235757949810246995393840000000000)
      constant := (11191310302170296785497897141305848064316395313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree020.table
  base := (-3633769358172288026777328103646167518981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-512874314061448579373447787465928614000000000000)
      constant := (2529788169549607477075218314231727500665730615171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21788023493793995073/10000000000000000000)
  centralHi := (217880234937939950731/100000000000000000000)
  directionLo := (223540404393553847249/100000000000000000000)
  directionHi := (894161617574215389/400000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree021.table
  base := (-2126478429697098716158293792847358045457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-29846518713579018839218022984556668000000000000)
      constant := (153806019042670784113271822753889097260270792543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree021.table
  base := (-4266800339085868710067653232767217425187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-59831864850134183292489102189842586000000000000)
      constant := (309062801979505724416556011457075614607159232813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223540404393553847249/100000000000000000000)
  centralHi := (894161617574215389/400000000000000000)
  directionLo := (114530375901172248339/50000000000000000000)
  directionHi := (229060751802344496679/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree022.table
  base := (-2401296165514123401640673164042258935739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-31266128275955090704063417881670913000000000000)
      constant := (168577516937035550471737793534348241060765290261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree022.table
  base := (-4814413332730567694948503245067064942621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-564099253240966719891356051951237934000000000000)
      constant := (3048817575472326905185673373365127282369731642411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114530375901172248339/50000000000000000000)
  centralHi := (229060751802344496679/100000000000000000000)
  directionLo := (117225577025746547391/50000000000000000000)
  directionHi := (234451154051493094783/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree023.table
  base := (-1319096625141968374117662255390877846503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-32685737838331162568908812778785158000000000000)
      constant := (184190691153641877923010506728252954638487910994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree023.table
  base := (-5286469868723733255441726298808972952441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-589711722830725790150310184193892594000000000000)
      constant := (3331273123382918758555732780710317853069586474031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117225577025746547391/50000000000000000000)
  centralHi := (234451154051493094783/100000000000000000000)
  directionLo := (119860188611459545793/50000000000000000000)
  directionHi := (239720377222919091587/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree024.table
  base := (-2841169742130175669184621082819107923091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-34105347400707234433754207675899403000000000000)
      constant := (200633277510282637567451932709486494288695070909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree024.table
  base := (-1422733229860532260392410385536274650141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-34184677356693603356070239802030403000000000000)
      constant := (201595118400883106239421866687459404772786087718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119860188611459545793/50000000000000000000)
  centralHi := (239720377222919091587/100000000000000000000)
  directionLo := (244876244000352769641/100000000000000000000)
  directionHi := (122438122000176384821/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree025.table
  base := (-6026922881508379440722010851243561796879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-71049913926166612597199205146027296000000000000)
      constant := (435790710083675383930815213522406132037207189121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree025.table
  base := (-754280127263779285096886696550297179371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-320468331005121965334109224339600957000000000000)
      constant := (1970478467013757643812442465776370372719048046644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244876244000352769641/100000000000000000000)
  centralHi := (122438122000176384821/50000000000000000000)
  directionLo := (249925769970889526953/100000000000000000000)
  directionHi := (124962884985444763477/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree026.table
  base := (-6315377827087833931746677412634465282437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-73889133050918756326889994940255786000000000000)
      constant := (471937778172150111248763392872257432809582875563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree026.table
  base := (-1264321209545974608007126850559836350891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (5000643105556751387113401102793716000000000000)
      linear := (-133309826320000600185434516184371314800000000000)
      constant := (853572743014263520836202321066823539494986587981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249925769970889526953/100000000000000000000)
  centralHi := (124962884985444763477/50000000000000000000)
  directionLo := (50975055121250693799/20000000000000000000)
  directionHi := (63718818901563367249/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree027.table
  base := (-6551953322203202886865066307336619385789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-76728352175670900056580784734484276000000000000)
      constant := (509694731844047495445017014259928658376551540211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree027.table
  base := (-6403565708591141037767727028115891141/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-38453422288320115065895928509139513000000000000)
      constant := (256073107621976651686574105315911021618651063808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975055121250693799/20000000000000000000)
  centralHi := (63718818901563367249/25000000000000000000)
  directionLo := (259730479026211600363/100000000000000000000)
  directionHi := (64932619756552900091/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree028.table
  base := (-3370048687489727790997991328678249683161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-39783785650211521893135787264356383000000000000)
      constant := (274525499751504186297319872631271416793178690839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree028.table
  base := (-6744602239929560228441207886139379346779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-717774070779521141445080845407165894000000000000)
      constant := (4965219076895733303489896662099750803050566152989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259730479026211600363/100000000000000000000)
  centralHi := (64932619756552900091/25000000000000000000)
  directionLo := (52899314685544660067/20000000000000000000)
  directionHi := (16531035839232706271/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree029.table
  base := (-3441305306636015145233730295724689432987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-41203395212587593757981182161470628000000000000)
      constant := (294998997210613670548084779956651080348772425013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree029.table
  base := (-6886439952271606218953975022216606436977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-743386540369280211704034977649820554000000000000)
      constant := (5335496394086355177676295735725004298028598729207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52899314685544660067/20000000000000000000)
  centralHi := (16531035839232706271/6250000000000000000)
  directionLo := (134589146084322771861/50000000000000000000)
  directionHi := (269178292168645543723/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree030.table
  base := (-1745442482013075416544486895611875351467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-42623004774963665622826577058584873000000000000)
      constant := (316264367824354637644689582181027754121053653066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree030.table
  base := (-1397004866897509804346429015079955844667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-17088866887978650710288646886499449200000000000)
      constant := (127113011749758414447044646892836966300295133333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134589146084322771861/50000000000000000000)
  centralHi := (269178292168645543723/100000000000000000000)
  directionLo := (273779963829806914273/100000000000000000000)
  directionHi := (136889981914903457137/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree031.table
  base := (-7039428115250845232724470812580447762349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-88085228674679474975343943911398236000000000000)
      constant := (676637542511278234688344549671059799330190203651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree031.table
  base := (-3521096758305142807326893966205066680291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-397305739774399176110971621067564937000000000000)
      constant := (3059467879738691395654198262050456801178450023381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273779963829806914273/100000000000000000000)
  centralHi := (136889981914903457137/50000000000000000000)
  directionLo := (139152779539677235359/50000000000000000000)
  directionHi := (278305559079354470719/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree032.table
  base := (-3528547128665893907028388201218350105031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-45462223899715809352517366852813363000000000000)
      constant := (361159894080295061993354485142422313359624848969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree032.table
  base := (-7059443952664568561511569093820158752629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-820223949138557422480897374377784534000000000000)
      constant := (6532005793135290492782390091537967862998526600339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139152779539677235359/50000000000000000000)
  centralHi := (278305559079354470719/100000000000000000000)
  directionLo := (70689682695874076313/25000000000000000000)
  directionHi := (282758730783496305253/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree033.table
  base := (-3517999313346591798222845768084710773267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-46881833462091881217362761749927608000000000000)
      constant := (384785850290121118325655941892984604559452604733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree033.table
  base := (-7037995070088405636535333541350005481363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-93981824303146276971094611846715466000000000000)
      constant := (773251331202350280119424611332737289844135560637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/25000000000000000000)
  centralHi := (282758730783496305253/100000000000000000000)
  directionLo := (143571424258202771101/50000000000000000000)
  directionHi := (287142848516405542203/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree034.table
  base := (-872143142010746657398017433451146702309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (4806462039174117057971358230290000000000000)
      linear := (-167133020845909872256775628536477000000000000)
      constant := (1415900003067017778215398803088695138540815276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree034.table
  base := (-54522199137664318006487994031064411759/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (43258158352567053521742224072610000000000000)
      linear := (-1507697038612587479236687956510543000000000000)
      constant := (12803939233497125977631228476974553089653690944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143571424258202771101/50000000000000000000)
  centralHi := (287142848516405542203/100000000000000000000)
  directionLo := (291461028396485796619/100000000000000000000)
  directionHi := (14573051419824289831/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree035.table
  base := (-430084610025060616261825137541034964629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-49721052586844024947053551544156098000000000000)
      constant := (434386388847118516865944006070846558434300170968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree035.table
  base := (-6882795240305481370970189514116385587561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-897061357907834633257759771105748514000000000000)
      constant := (7856228074419127699286597577971749319049371477951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291461028396485796619/100000000000000000000)
  centralHi := (14573051419824289831/5000000000000000000)
  directionLo := (59143231800015385803/20000000000000000000)
  directionHi := (36964519875009616127/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree036.table
  base := (-1349858975069706267709426597436602623287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-20456264859688038724759578576508137200000000000)
      constant := (184143474594429235453975600819752024120399434713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree036.table
  base := (-6750519914470818843187045677148393592341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-102519314166399300390745989260933686000000000000)
      constant := (925099695780202062468498962091665024097488901659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59143231800015385803/20000000000000000000)
  centralHi := (36964519875009616127/12500000000000000000)
  directionLo := (37488865495633429043/12500000000000000000)
  directionHi := (59982184793013486469/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree037.table
  base := (-822689634496747867009238768743179087903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-52560271711596168676744341338384588000000000000)
      constant := (487111152806753072092868726351457914568241256388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree037.table
  base := (-3291279162178107719824408471934069862911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-474143148543676386887834017795528917000000000000)
      constant := (4404834730701799213974237286706739572796205099801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/12500000000000000000)
  centralHi := (59982184793013486469/20000000000000000000)
  directionLo := (304047821786971758143/100000000000000000000)
  directionHi := (4750747215421433721/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree038.table
  base := (-1275693946343713917594480808444078938481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-21591952509588896216635894494199533200000000000)
      constant := (205857239570232141613377884449628781130538315519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree038.table
  base := (-3189677457720285076370361105578785458913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-486949383338555922017311083916856247000000000000)
      constant := (4653766204265961274188290330014850294837685547783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304047821786971758143/100000000000000000000)
  centralHi := (4750747215421433721/1562500000000000000)
  directionLo := (4814518487847983493/1562500000000000000)
  directionHi := (308129183222270943553/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree039.table
  base := (-6140521289295600914297698577388770637269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-110798981672696624812870262265226156000000000000)
      constant := (1085907920027118414904935405400934684587362608731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree039.table
  base := (-6141273945922855140963483466064551600849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-111056804029652323810397366675151906000000000000)
      constant := (1091052894673641129107598952184061432727245365151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4814518487847983493/1562500000000000000)
  centralHi := (308129183222270943553/100000000000000000000)
  directionLo := (312157186643276718491/100000000000000000000)
  directionHi := (78039296660819179623/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree040.table
  base := (-1466993534434798825020106478825729704553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-56819100398724384271280526029727323000000000000)
      constant := (572043272508149134348626549464274337800221594894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree040.table
  base := (-366788390302402137600548793638813763773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-512561852928314992276265216159510907000000000000)
      constant := (5172746073052524989391581754517506222024991712344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312157186643276718491/100000000000000000000)
  centralHi := (78039296660819179623/25000000000000000000)
  directionLo := (79033467907932513561/25000000000000000000)
  directionHi := (63226774326346010849/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree041.table
  base := (-5561076691874048014440335543524358829691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-116477419922200912272251841853683136000000000000)
      constant := (1203821311178599338924026081782372772053808564309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree041.table
  base := (-5561621203227762311165891322124440814719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1050736175446389054811484564561676474000000000000)
      constant := (10885573919336183164835559568785939485038676581529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/25000000000000000000)
  centralHi := (63226774326346010849/20000000000000000000)
  directionLo := (320061151051933911147/100000000000000000000)
  directionHi := (80015287762983477787/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree042.table
  base := (-2610016611705530354263743230863863022157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-59658319523476528000971315823955813000000000000)
      constant := (632555796108375864705963310959672771110203615843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree042.table
  base := (-261024826291306792062442027251219559553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-11959429389290534723004874408937012600000000000)
      constant := (127107953399043206771439933253491803358381884894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320061151051933911147/100000000000000000000)
  centralHi := (80015287762983477787/25000000000000000000)
  directionLo := (323940821806252962971/100000000000000000000)
  directionHi := (80985205451563240743/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree043.table
  base := (-4845011866723786195168839666297804191633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-122155858171705199731633421442140116000000000000)
      constant := (1327956872630597992863274444097590242800649030367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree043.table
  base := (-2422703084360791484124188341317708127511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-550980557312953597664696414523492897000000000000)
      constant := (6003956613222189829136843442289709451070088318401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323940821806252962971/100000000000000000000)
  centralHi := (80985205451563240743/25000000000000000000)
  directionLo := (10242955451393444301/3125000000000000000)
  directionHi := (327774574444590217633/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree044.table
  base := (-4436151144173995629447567908502771277793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-124995077296457343461324211236368606000000000000)
      constant := (1392356727710438416554813385578545888759515384207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree044.table
  base := (-1109121701596413497788896758977371513807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-563786792107833132794173480644820227000000000000)
      constant := (6295081204765529141086762745089577457303332035474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10242955451393444301/3125000000000000000)
  centralHi := (327774574444590217633/100000000000000000000)
  directionLo := (331564001773645345753/100000000000000000000)
  directionHi := (165782000886822672877/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree045.table
  base := (-1996782644843931403341269877145318848943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-63917148210604743595507500515298548000000000000)
      constant := (729155403607470558851961000010073657138821913057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree045.table
  base := (-3993851105464104002240628083966306285813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-128131783756158370649700121503588346000000000000)
      constant := (1465162249583276390589023475699692540961391056187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331564001773645345753/100000000000000000000)
  centralHi := (165782000886822672877/50000000000000000000)
  directionLo := (167655303295165385437/50000000000000000000)
  directionHi := (2682484852722646167/800000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree046.table
  base := (-879337148995152090812116680063945261403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-65336757772980815460352895412412793000000000000)
      constant := (762909411021273468562127392768902320529186281194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree046.table
  base := (-219849501847319339710546388425892572187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-589399261697592203053127612887474887000000000000)
      constant := (6898402085680623708369539427345883683240310178536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167655303295165385437/50000000000000000000)
  centralHi := (2682484852722646167/800000000000000000)
  directionLo := (339015808645846562389/100000000000000000000)
  directionHi := (33901580864584656239/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree047.table
  base := (-3007578967858293808295268147168020799083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-133512734670713774650396580619054076000000000000)
      constant := (1594880533337042585422696580282798261811990722917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree047.table
  base := (-1503893178194180506982063320554012866037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-602205496492471738182604679008802217000000000000)
      constant := (7210596033130569732575872200829496022988459227667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339015808645846562389/100000000000000000000)
  centralHi := (33901580864584656239/10000000000000000000)
  directionLo := (342680950931940382653/100000000000000000000)
  directionHi := (171340475465970191327/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree048.table
  base := (-2464320829363997140497622544426724623603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-136351953795465918380087370413282566000000000000)
      constant := (1665495743574247561412232821270631205877308578397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree048.table
  base := (-492899510845919009968422617073607477857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-27333854723882278813870299783561313200000000000)
      constant := (334658270657891158984563307829104239999282960143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342680950931940382653/100000000000000000000)
  centralHi := (171340475465970191327/50000000000000000000)
  directionLo := (346307305368282133817/100000000000000000000)
  directionHi := (173153652684141066909/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree049.table
  base := (-1887627504556399783990923667765205280633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-139191172920218062109778160207511056000000000000)
      constant := (1737664289262544623787782967110831380594373941367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree049.table
  base := (-1887778136585073429083619144014318933819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1255635932164461616883117622502913754000000000000)
      constant := (15712093062335026260177018391759991703211328109629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346307305368282133817/100000000000000000000)
  centralHi := (173153652684141066909/50000000000000000000)
  directionLo := (69979215591849067547/20000000000000000000)
  directionHi := (43737009744905667217/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree050.table
  base := (-311900187770418032641381050211282057/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-71015196022485102919734475000869773000000000000)
      constant := (905693017479639422346965870009285933636005771264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree050.table
  base := (-319417897911137677350256513663134362461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-640624200877110343571035877372784207000000000000)
      constant := (8189301757218706150896723276363986419868083807702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69979215591849067547/20000000000000000000)
  centralHi := (43737009744905667217/12500000000000000000)
  directionLo := (70689682695874076313/20000000000000000000)
  directionHi := (176724206739685190783/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree051.table
  base := (-634104451637016107762094544504010780247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (9612924078348234115942716460580000000000000)
      linear := (-501278931383122316848303597909924000000000000)
      constant := (6528238298827220607915863359873069699632359577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree051.table
  base := (-634213964836531965146065070327572968389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (9612924078348234115942716460580000000000000)
      linear := (-502445548382921859823539364470674000000000000)
      constant := (6558689942819831488380017683141688778378361099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/20000000000000000000)
  centralHi := (176724206739685190783/50000000000000000000)
  directionLo := (44620674967389285099/12500000000000000000)
  directionHi := (356965399739114280793/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree052.table
  base := (42658251082910300114493380962745766253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-147708830294474493298850529590196526000000000000)
      constant := (1963488696271373357330457564453466881482077464253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree052.table
  base := (42564841884293106891242765497099174361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1332473340933738827659980019230877734000000000000)
      constant := (17753739317731127633540525603347150192091210003249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44620674967389285099/12500000000000000000)
  centralHi := (356965399739114280793/100000000000000000000)
  directionLo := (360448071475944131253/100000000000000000000)
  directionHi := (180224035737972065627/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree053.table
  base := (188179923219465922776070362909366163159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-75274024709613318514270659692212508000000000000)
      constant := (1020934720642701525469806965733749465006223314318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree053.table
  base := (752640002275719481218345785212677310353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1358085810523497897918934151473532394000000000000)
      constant := (18462363158752099256932458681065863596615976475177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360448071475944131253/100000000000000000000)
  centralHi := (180224035737972065627/50000000000000000000)
  directionLo := (363897413910224166439/100000000000000000000)
  directionHi := (9097435347755604161/2500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree054.table
  base := (1496058888406124561986122583971958165487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-153387268543978780758232109178653506000000000000)
      constant := (2121803039062077139176558071866107461707341307487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree054.table
  base := (747995443733016416847535950093423412879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-76872126672958720454327126873121503000000000000)
      constant := (1065834638616890268141470688951800213277310426879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363897413910224166439/100000000000000000000)
  centralHi := (9097435347755604161/2500000000000000000)
  directionLo := (183657183000264577231/50000000000000000000)
  directionHi := (367314366000529154463/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree055.table
  base := (1136329190131605777444596168769305997537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-78113243834365462243961449486440998000000000000)
      constant := (1101644718038488012396788340022058485332754439537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree055.table
  base := (284075042841576486291636626322097281423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-704655374851508019218421207979420857000000000000)
      constant := (9960859926709666969222270686032377492129847179228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183657183000264577231/50000000000000000000)
  centralHi := (367314366000529154463/100000000000000000000)
  directionLo := (37069982342886591599/10000000000000000000)
  directionHi := (370699823428865915991/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree056.table
  base := (616500726945052678316467668149499435457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-31813141358696613643522737753422097200000000000)
      constant := (457265717553937563077550352919816072618610597457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree056.table
  base := (7706135228591326740257430911209132909/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5518801800000000000000000000000000000000000000
      center := (55188018)
      previous := (27594009)
      next := (27594009)
      square := (500064310555675138711340110279371600000000000)
      linear := (-28698464385855502173915930964029927480000000000)
      constant := (413449036794966471601464994417321805394985137448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37069982342886591599/10000000000000000000)
  centralHi := (370699823428865915991/100000000000000000000)
  directionLo := (46756830167837185011/12500000000000000000)
  directionHi := (374054641342697480089/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree057.table
  base := (61337227235663064555410323618473822243/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-80952462959117605973652239280669488000000000000)
      constant := (1185460228507448010363803605786717907314067527776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree057.table
  base := (3925540243291459592062826153789208596423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-162281743209170464328305631160461226000000000000)
      constant := (2381913236221147306471865352806471119345841514423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/12500000000000000000)
  centralHi := (374054641342697480089/100000000000000000000)
  directionLo := (75475927375511120989/20000000000000000000)
  directionHi := (188689818438777802473/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree058.table
  base := (4801885009727272182245746693315700496477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-164744145042987355676995268355567466000000000000)
      constant := (2457065012859458080226972466119844379037898978477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree058.table
  base := (2400924444162254336135664880242030415841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-743074079236146624606852406343402847000000000000)
      constant := (11108010719344729679572301335129965950472990296569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75475927375511120989/20000000000000000000)
  centralHi := (188689818438777802473/50000000000000000000)
  directionLo := (76135118296265201431/20000000000000000000)
  directionHi := (95168897870331501789/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree059.table
  base := (5711402611591647418209552978205866148247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-167583364167739499406686058149795956000000000000)
      constant := (2544762229478238702249028570785526516566391450247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree059.table
  base := (5711371761286014699127486796052423455609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1511760628062052319472658944929460354000000000000)
      constant := (23008858549774350788141362173117493643305885846481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76135118296265201431/20000000000000000000)
  centralHi := (95168897870331501789/25000000000000000000)
  directionLo := (19197162652946859709/5000000000000000000)
  directionHi := (383943253058937194181/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree060.table
  base := (6654128316318314887782663602256639841611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-170422583292491643136376847944024446000000000000)
      constant := (2634012085310023535282754294969853970011019167611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree060.table
  base := (1330820392806544869452802814007066333323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-34163846614484697549591401714935889200000000000)
      constant := (529238450419946067326391154292618931385034651323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19197162652946859709/5000000000000000000)
  centralHi := (383943253058937194181/100000000000000000000)
  directionLo := (96795834488532086743/25000000000000000000)
  directionHi := (387183337954128346973/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree061.table
  base := (7630056248829384662328851782628639420453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-173261802417243786866067637738252936000000000000)
      constant := (2724814562341817893729061038720414410841748318453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree061.table
  base := (1907508433915979451085782249951055677711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-781492783620785229995283604707384837000000000000)
      constant := (12318318218546389886587597448392955451860516866798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/25000000000000000000)
  centralHi := (387183337954128346973/100000000000000000000)
  directionLo := (19519826639158609849/5000000000000000000)
  directionHi := (390396532783172196981/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree062.table
  base := (4319590748905707969968961094297962910889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-88050510770997965297879213766240713000000000000)
      constant := (1408584822757764928387925670621503389582748584889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree062.table
  base := (8639162262029323926110776350069635239413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1588598036831329530249521341657424334000000000000)
      constant := (25471576921518265109297154335522596103423079476717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19519826639158609849/5000000000000000000)
  centralHi := (390396532783172196981/100000000000000000000)
  directionLo := (393583496133849752841/100000000000000000000)
  directionHi := (196791748066924876421/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree063.table
  base := (121018749439421157426829301848220000411/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-17894024066674807432544921732670991600000000000)
      constant := (291107732223568786066867189103282584630841011288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree063.table
  base := (9681483517729281610422927355982871496983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-179356722935676511167608385988897666000000000000)
      constant := (2924505734566346062333774223371601517992621374983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393583496133849752841/100000000000000000000)
  centralHi := (196791748066924876421/50000000000000000000)
  directionLo := (198372430070792475251/50000000000000000000)
  directionHi := (396744860141584950503/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree064.table
  base := (215140163652325677507541743772141558819/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 613200200000000000000000000000000000000000000
      center := (6132002)
      previous := (3066001)
      next := (3066001)
      square := (55562701172852793190148901142152400000000000)
      linear := (-3635589195830004361102800142418768120000000000)
      constant := (60130751639212896789787775261725643071480612819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree064.table
  base := (5378497067477338468324494884453721890561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-819911488005423835383714803071366827000000000000)
      constant := (13591780206448986564243865036533579049931637249049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198372430070792475251/50000000000000000000)
  centralHi := (396744860141584950503/100000000000000000000)
  directionLo := (199940615976711621563/50000000000000000000)
  directionHi := (399881231953423243127/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree065.table
  base := (593285165050958049511152917986132956237/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-18461867891625236178483079691516689600000000000)
      constant := (310355041586283194577738701700814361634911196474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree065.table
  base := (1186569129451788782868328236844015099411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (2500321552778375693556700551396858000000000000)
      linear := (-166543544560060674102638373838538831400000000000)
      constant := (2806060324912815219549178167114389250249283028699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/50000000000000000000)
  centralHi := (399881231953423243127/100000000000000000000)
  directionLo := (16119727803578280599/4000000000000000000)
  directionHi := (6296768673272765859/1562500000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree066.table
  base := (2601516579614940733289037010852350057081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-37491579608200901102904317341879077200000000000)
      constant := (640423163309234584698072276789290327327360403081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree066.table
  base := (13007572635247754738061038974964182375849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-187894212798929534587259763403115886000000000000)
      constant := (3216853339403719281655038901159041664128535409849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16119727803578280599/4000000000000000000)
  centralHi := (6296768673272765859/1562500000000000000)
  directionLo := (203040655355171936177/50000000000000000000)
  directionHi := (81216262142068774471/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree067.table
  base := (1418264495166726997143483383235049901261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-19029711716575664924421237650362387600000000000)
      constant := (330223377781085919234729186116591954307316127261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree067.table
  base := (886414761162193279382890974052068929413/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-858330192390062440772146001435348817000000000000)
      constant := (14928395387408916561747215432274474881054741493736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203040655355171936177/50000000000000000000)
  centralHi := (81216262142068774471/20000000000000000000)
  directionLo := (409146118798715381857/100000000000000000000)
  directionHi := (204573059399357690929/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree068.table
  base := (1923860970742829104372066888021902889339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (4806462039174117057971358230290000000000000)
      linear := (-334145910537212444591527969373447000000000000)
      constant := (5889107775877854664873132783198458471011989804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree068.table
  base := (15390880265847761185948805786968843637051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (9548100)
      previous := (4774050)
      next := (4774050)
      square := (86516316705134107043484448145220000000000000)
      linear := (-6028625793667418518350332647451046000000000000)
      constant := (106491125826680668671848883996325920159309266531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409146118798715381857/100000000000000000000)
  centralHi := (204573059399357690929/50000000000000000000)
  directionLo := (103047034815379998333/25000000000000000000)
  directionHi := (412188139261519993333/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree069.table
  base := (8316154959014686264977292790182565181847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-97987777707630468351796978046040428000000000000)
      constant := (1753563681061635069791870786556952928905108083847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree069.table
  base := (16632303505808001826373675249747127168139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-196431702662182558006911140817334106000000000000)
      constant := (3523234864835932268738542771526347685644641342139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/25000000000000000000)
  centralHi := (412188139261519993333/100000000000000000000)
  directionLo := (103801968239918227719/25000000000000000000)
  directionHi := (415207872959672910877/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree070.table
  base := (17906910213591949941601633969682028056923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-198814774540013080433284745886309346000000000000)
      constant := (3611902977146635664947088520615222537704553974923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree070.table
  base := (3581380946231529632772293846186551757283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (5000643105556751387113401102793716000000000000)
      linear := (-358699558709880418464230879919732322800000000000)
      constant := (6531265200288975331239177032914794770869432917547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103801968239918227719/25000000000000000000)
  centralHi := (415207872959672910877/100000000000000000000)
  directionLo := (41820580267078738683/10000000000000000000)
  directionHi := (418205802670787386831/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree071.table
  base := (19214687649725985500273925721911392945951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-201653993664765224162975535680537836000000000000)
      constant := (3718231136452590741721804270097946757433678711951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree071.table
  base := (4803670740510908581540596920793838289977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-909555131569580581290054265920658137000000000000)
      constant := (16808785995318548820227437152346969008836339895586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41820580267078738683/10000000000000000000)
  centralHi := (418205802670787386831/100000000000000000000)
  directionLo := (21059119699511375707/5000000000000000000)
  directionHi := (421182393990227514141/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree072.table
  base := (20555641383962307123007897451975110168647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-204493212789517367892666325474766326000000000000)
      constant := (3826111837458124045832350453259865631752181870647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree072.table
  base := (10277818687834441335079183484322478542779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-102484596262717790713281259115776163000000000000)
      constant := (1921825096021987966986997429334009399534638956779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21059119699511375707/5000000000000000000)
  centralHi := (421182393990227514141/100000000000000000000)
  directionLo := (424138096175244457879/100000000000000000000)
  directionHi := (10603452404381111447/2500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree073.table
  base := (21929770708357456776931471004517084560171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-207332431914269511622357115268994816000000000000)
      constant := (3935545077992680227006483245604579217528568846171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree073.table
  base := (21929767280881934966855661101776332580071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1870335202318679303098016796326625594000000000000)
      constant := (35582165195649294393395145946859266329201472394639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424138096175244457879/100000000000000000000)
  centralHi := (10603452404381111447/2500000000000000000)
  directionLo := (427073342936529576179/100000000000000000000)
  directionHi := (21353667146826478809/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree074.table
  base := (933483001112904061185078919847339897369/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1226400400000000000000000000000000000000000000
      center := (12264004)
      previous := (6132002)
      next := (6132002)
      square := (111125402345705586380297802284304800000000000)
      linear := (-8406866041560866214081916202528932240000000000)
      constant := (161861234249268653135383085124842052932673251369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree074.table
  base := (11668536048465270191162467467854489170987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-947973835954219186678485464284640127000000000000)
      constant := (18292756188186173883530373690914372217874617816883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427073342936529576179/100000000000000000000)
  centralHi := (21353667146826478809/5000000000000000000)
  directionLo := (85997710636226654437/20000000000000000000)
  directionHi := (214994276590566636093/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree075.table
  base := (24777553841986753993156196574756803581429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-213010870163773799081738694857451796000000000000)
      constant := (4159069170641094402264226170662176103287464895429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree075.table
  base := (24777551335686340401089281727472959590541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-213506682388688604846213895645770546000000000000)
      constant := (4178099250788391689859051292106992271577558296541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85997710636226654437/20000000000000000000)
  centralHi := (214994276590566636093/50000000000000000000)
  directionLo := (54110516463794083409/12500000000000000000)
  directionHi := (432884131710352667273/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree076.table
  base := (5250241346001849184512676914761399022993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-43170017857705188562285896930336057200000000000)
      constant := (854632003986103307793145555359984397365895560993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree076.table
  base := (6562801146691278078315585952961038070089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-973586305543978256937439596527294787000000000000)
      constant := (19317153913247340391746340072935205444310756993602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54110516463794083409/12500000000000000000)
  centralHi := (432884131710352667273/100000000000000000000)
  directionLo := (435760469875879901461/100000000000000000000)
  directionHi := (217880234937939950731/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree077.table
  base := (13879016668927460205841156132472979531659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-109344654206639043270560137222954388000000000000)
      constant := (2194401701507255296689809697675413145592046025659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree077.table
  base := (27758031505064102956467175479924758424053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-1972785080677715584133833325297244234000000000000)
      constant := (39679756075047046014656995031267348551276144298477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435760469875879901461/100000000000000000000)
  centralHi := (217880234937939950731/50000000000000000000)
  directionLo := (342670270466579849/78125000000000000)
  directionHi := (438617946197222206721/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree078.table
  base := (7324508341906780390593370313719432951053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-110764263769015115135405532120068633000000000000)
      constant := (2252999659489862560312774713050772599294722898106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree078.table
  base := (29298031800318370466936226440380334996361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-222044172251941628265865273059988766000000000000)
      constant := (4526581999415894164894569747611856465479177822361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342670270466579849/78125000000000000)
  centralHi := (438617946197222206721/100000000000000000000)
  directionLo := (441456926943151492193/100000000000000000000)
  directionHi := (220728463471575746097/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree079.table
  base := (6174241313724245319821351820337602792507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-44873549332556474800100370806873151200000000000)
      constant := (924949553411499899313823941491007405049429254507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree079.table
  base := (6174241045668935950158753822724198097671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (5000643105556751387113401102793716000000000000)
      linear := (-404802003971446744930348317956510710800000000000)
      constant := (8362550715768938160969111113175147624024916453039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441456926943151492193/100000000000000000000)
  centralHi := (220728463471575746097/50000000000000000000)
  directionLo := (444277766679712066469/100000000000000000000)
  directionHi := (44427776667971206647/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree080.table
  base := (1014923522806800492742114750083129705263/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-113603482893767258865096321914297123000000000000)
      constant := (2372524373300423678012267094298849352151457012208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree080.table
  base := (16238775791848384665513404699559404678999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1024811244723496397455347861012604107000000000000)
      constant := (21450151410841444994413614345523762068746940516991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444277766679712066469/100000000000000000000)
  centralHi := (44427776667971206647/10000000000000000000)
  directionLo := (447080808787107694499/100000000000000000000)
  directionHi := (894161617574215389/200000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree081.table
  base := (34117071673579608854046982504328318269663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-230046184912286661459883433622822736000000000000)
      constant := (4866902257065134459818224493247966567893105027663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree081.table
  base := (34117070693501697139621919801925749790743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-230581662115194651685516650474206986000000000000)
      constant := (4889098413165265279634989552622846946784167828743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447080808787107694499/100000000000000000000)
  centralHi := (894161617574215389/200000000000000000)
  directionLo := (112466596486900287129/25000000000000000000)
  directionHi := (449866385947601148517/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree082.table
  base := (3578976325036065849320474261641639273993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-23288540403703880518957422341705122600000000000)
      constant := (499030829799185094418316661606770602855701811993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree082.table
  base := (35789762412285104449131278117879413975723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2100847428626510935428603986510517534000000000000)
      constant := (45117502265243962624514163660617976228160826243507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112466596486900287129/25000000000000000000)
  centralHi := (449866385947601148517/100000000000000000000)
  directionLo := (113158705151597183561/25000000000000000000)
  directionHi := (90526964121277746849/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree083.table
  base := (7499125466851466844609750596297017684973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-47144924632358189783853002642255943200000000000)
      constant := (1023053373798995353083782026330961775869144902973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree083.table
  base := (1171738331800779606402164313286672821707/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1063229949108135002843779059376586097000000000000)
      constant := (23123576229287250166150205943595013051755813653808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113158705151597183561/25000000000000000000)
  centralHi := (90526964121277746849/20000000000000000000)
  directionLo := (455386425407257161607/100000000000000000000)
  directionHi := (56923303175907145201/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree084.table
  base := (4904332977408934274501653108529605772049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-119281921143271546324477901502754103000000000000)
      constant := (2620888984874760726651328242096664036306832024196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree084.table
  base := (1226083225203113636361190344447249821403/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-119559575989223837552584013944212603000000000000)
      constant := (2632824238646456776014596506655087340394742710448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455386425407257161607/100000000000000000000)
  centralHi := (56923303175907145201/12500000000000000000)
  directionLo := (458121503604688993357/100000000000000000000)
  directionHi := (229060751802344496679/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree085.table
  base := (41006872616167245115429014714665771295393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (9612924078348234115942716460580000000000000)
      linear := (-835304710765727461517808279583864000000000000)
      constant := (18580766781944248628757732812640172917672824337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree085.table
  base := (41006872092218503408196362295847046000181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (9548100)
      previous := (4774050)
      next := (4774050)
      square := (86516316705134107043484448145220000000000000)
      linear := (-7535241651888540298288811014666026000000000000)
      constant := (167988075342688527549077477733728731799143282061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458121503604688993357/100000000000000000000)
  centralHi := (229060751802344496679/50000000000000000000)
  directionLo := (46084034945395433521/10000000000000000000)
  directionHi := (460840349453954335211/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree086.table
  base := (21406126824913748208521459728785008099051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-122121140268023690054168691296982593000000000000)
      constant := (2749728879730883353948372071394437326616698465051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree086.table
  base := (42812253201840838512149975562519601290249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2203297306985547216464420515481136174000000000000)
      constant := (49720304891764061203621042230411002474679542518241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46084034945395433521/10000000000000000000)
  centralHi := (460840349453954335211/100000000000000000000)
  directionLo := (463543248580609174157/100000000000000000000)
  directionHi := (231771624290304587079/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree087.table
  base := (4465080685702935120171579858900565797499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-24708149966079952383802817238819367600000000000)
      constant := (563062644799531661206429706006442553710697731499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree087.table
  base := (4465080647400501515135193717019940990279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-24765664184170069852481940530264342600000000000)
      constant := (565623218301380432439066080849354934296136404279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463543248580609174157/100000000000000000000)
  centralHi := (231771624290304587079/50000000000000000000)
  directionLo := (233115239165356856213/50000000000000000000)
  directionHi := (466230478330713712427/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree088.table
  base := (46522532184571964600268429117945202523001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-249920718785551667567718962182422166000000000000)
      constant := (5763347665419423722643895167809949336880723589001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree088.table
  base := (1860901274284079193039687023065197861189/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11037603600000000000000000000000000000000000000
      center := (110376036)
      previous := (55188018)
      next := (55188018)
      square := (1000128621111350277422680220558743200000000000)
      linear := (-90180889846602614279293151198657819760000000000)
      constant := (2084236321547736676904514623628510315448430016701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233115239165356856213/50000000000000000000)
  centralHi := (466230478330713712427/100000000000000000000)
  directionLo := (93780461620597237913/20000000000000000000)
  directionHi := (234451154051493094783/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree089.table
  base := (4842742958770023132944562373775128304273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-25275993791030381129740975197665065600000000000)
      constant := (589762141159686884208197277848810857931029322273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree089.table
  base := (48427429307738031793413482090339743590221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2280134715754824427241282912209100154000000000000)
      constant := (53319760065274189044075607472676101973686250585989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93780461620597237913/20000000000000000000)
  centralHi := (234451154051493094783/50000000000000000000)
  directionLo := (471558999664018147533/100000000000000000000)
  directionHi := (235779499832009073767/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree090.table
  base := (5036549902877729562513806309737084680159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-25559915703505595502710054177087914600000000000)
      constant := (603344768641225733296891495485925525366452174159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree090.table
  base := (50365498789440721396024185925289422401909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-256194131704953721944470782716861646000000000000)
      constant := (6060849525095570464422282382259663184373675395909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471558999664018147533/100000000000000000000)
  centralHi := (235779499832009073767/50000000000000000000)
  directionLo := (237100403723797540683/50000000000000000000)
  directionHi := (474200807447595081367/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree091.table
  base := (10467348095233261013826683624732610248871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-51687675231961619751358266313021527200000000000)
      constant := (1234165297953718114830726055554562092705648734871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree091.table
  base := (26168370135784569848591137149697787334087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1165679827467171283879595588347204737000000000000)
      constant := (27894782509802873406410893681604216667976882684783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237100403723797540683/50000000000000000000)
  centralHi := (474200807447595081367/100000000000000000000)
  directionLo := (119206994709772805501/25000000000000000000)
  directionHi := (95365595767818244401/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree092.table
  base := (27170576951644100650435418612007237537277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-130638797642280121243241060679668063000000000000)
      constant := (3154878910792188573061790407842484933296528819277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree092.table
  base := (54341153728396101110561834616377022134429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2356972124524101638018145308937064134000000000000)
      constant := (57045517945801110752525597732175499804170633035861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119206994709772805501/25000000000000000000)
  centralHi := (95365595767818244401/20000000000000000000)
  directionLo := (479440754445838183173/100000000000000000000)
  directionHi := (239720377222919091587/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree093.table
  base := (14094684821956914965097687282561066996871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-132058407204656193108086455576782308000000000000)
      constant := (3225120840895599120884603031563959853821946965742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree093.table
  base := (14094684784583733926436999411170950188359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-132365810784103372682061080065539933000000000000)
      constant := (3239750250213920179698448626218275292896917764718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479440754445838183173/100000000000000000000)
  centralHi := (239720377222919091587/50000000000000000000)
  directionLo := (482039368354303801269/100000000000000000000)
  directionHi := (48203936835430380127/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree094.table
  base := (29224748305531874318392957955669556170747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-133478016767032264972931850473896553000000000000)
      constant := (3296139035165827732258766158848967611889066472747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree094.table
  base := (29224748241643988167640863220015710733831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1204098531851809889268026786711186727000000000000)
      constant := (29799762346627358534407615494948440525130729218479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482039368354303801269/100000000000000000000)
  centralHi := (48203936835430380127/10000000000000000000)
  directionLo := (121156012093714798559/25000000000000000000)
  directionHi := (484624048374859194237/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree095.table
  base := (30276712928652805629238457053372559250653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-134897626329408336837777245371010798000000000000)
      constant := (3367933493578820316521220347742767364410061348653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree095.table
  base := (15138356437024371746280287733769769866101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1216904766646689424397503852832514057000000000000)
      constant := (30448789256797654775631984698532122182226239577818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121156012093714798559/25000000000000000000)
  centralHi := (484624048374859194237/100000000000000000000)
  directionLo := (487195016274858402651/100000000000000000000)
  directionHi := (121798754068714600663/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree096.table
  base := (62690527013416616258063080763784174659839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-272634471783568817405245280536250086000000000000)
      constant := (6881008432228876822128249296477144179291241033839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree096.table
  base := (62690526920082848826707212829835828338139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-273269111431459768783773537545298086000000000000)
      constant := (6912185107169159063537495820185507815520562512139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487195016274858402651/100000000000000000000)
  centralHi := (121798754068714600663/25000000000000000000)
  directionLo := (489752488000705539283/100000000000000000000)
  directionHi := (122438122000176384821/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree097.table
  base := (32430400034206521670050221405095346374381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-137736845454160480567468035165239288000000000000)
      constant := (3513851202755843967182703301894612104954198520381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree097.table
  base := (8107599998581299504357382832173049576309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1242517236236448494656457985075168717000000000000)
      constant := (31767893522871880710206338578447549292264466931124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489752488000705539283/100000000000000000000)
  centralHi := (122438122000176384821/25000000000000000000)
  directionLo := (492296673889538789201/100000000000000000000)
  directionHi := (246148336944769394601/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree098.table
  base := (33532122506562793315053001427661957916499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-139156455016536552432313430062353533000000000000)
      constant := (3587974453488980434386720936469536434633943850499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree098.table
  base := (67064244944964455166636118445986619345097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2510646942062656059571870102392992094000000000000)
      constant := (64875941757015487444484050317347448430088180723873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492296673889538789201/100000000000000000000)
  centralHi := (246148336944769394601/50000000000000000000)
  directionLo := (30926736179444908387/6250000000000000000)
  directionHi := (494827778871118534193/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree099.table
  base := (34650430919956904942322296035537833765433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-140576064578912624297158824959467778000000000000)
      constant := (3662873968302135020094773316432270830237651343433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree099.table
  base := (13860172356333991412857049144939938920357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-56361320258942558440684982991903261200000000000)
      constant := (1471780668847436751100375987792382532469753482357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30926736179444908387/6250000000000000000)
  centralHi := (494827778871118534193/100000000000000000000)
  directionLo := (49734600266046801863/10000000000000000000)
  directionHi := (497346002660468018631/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree100.table
  base := (71570650542425247513325880543549772322221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-283991348282577392324008439713164046000000000000)
      constant := (7477099494371138782761118541659294995489701908221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree100.table
  base := (17892662623164628761285634813245680438419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1280935940621087100044889183439150707000000000000)
      constant := (33799176034466352804207188305820881200457715663542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49734600266046801863/10000000000000000000)
  centralHi := (497346002660468018631/100000000000000000000)
  directionLo := (499851539941779053907/100000000000000000000)
  directionHi := (124962884985444763477/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree101.table
  base := (14774722223078431146112615925559528357217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-57366113481465907210739845901478507200000000000)
      constant := (1526000716052483237754760943950226371452755679217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree101.table
  base := (36936805536435572265227806812205202171747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1293742175415966635174366249560478037000000000000)
      constant := (34490303834635022602589733634312362730574006263723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499851539941779053907/100000000000000000000)
  centralHi := (124962884985444763477/25000000000000000000)
  directionLo := (31396536284003876631/6250000000000000000)
  directionHi := (502344580544062026097/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree102.table
  base := (38104871777230010109889699864524915305407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (4806462039174117057971358230290000000000000)
      linear := (-501158800228515016926280310210417000000000000)
      constant := (13467924211530711614149595871393943826475062863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree102.table
  base := (19052435879532969126678634835012367683079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (4806462039174117057971358230290000000000000)
      linear := (-502325417228314559901516076771167000000000000)
      constant := (13528815243950680673446689216728791417499570222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31396536284003876631/6250000000000000000)
  centralHi := (502344580544062026097/100000000000000000000)
  directionLo := (504825309608988701001/100000000000000000000)
  directionHi := (252412654804494350501/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree103.table
  base := (15715809571208570766513854420525772225811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (5780)
      previous := (2890)
      next := (2890)
      square := (52373174825952298228060044436000000000000)
      linear := (-5514355842338275492752960865224800000000000)
      constant := (149693078261233848905497313624776098173259379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree103.table
  base := (78579047825007423156415615662743372770613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (260100)
      previous := (130050)
      next := (130050)
      square := (2356792867167853420262701999620000000000000)
      linear := (-248723658215802753404339783542866000000000000)
      constant := (6766633967209176586648055353601913512576364413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504825309608988701001/100000000000000000000)
  centralHi := (252412654804494350501/50000000000000000000)
  directionLo := (507293907751347807471/100000000000000000000)
  directionHi := (31705869234459237967/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree104.table
  base := (40490762008600549046547779760981271337333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-147674112390792983621385799445039003000000000000)
      constant := (4049015503280299053094122671929485040901534315333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree104.table
  base := (80981523990688816138991610431495139464793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2664321759601210481125594895848920054000000000000)
      constant := (73211576246464675140947765822087668097847753225137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507293907751347807471/100000000000000000000)
  centralHi := (31705869234459237967/6250000000000000000)
  directionLo := (50975055121250693799/10000000000000000000)
  directionHi := (509750551212506937991/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree105.table
  base := (5213573252221162445053789623884230753241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-149093721953169055486231194342153248000000000000)
      constant := (4128572602418875237886563916801602114864341273928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree105.table
  base := (10427146501611447422427081290436729196943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-149440790510609419521363834893976373000000000000)
      constant := (4147220353555331400527264911605309498618225739772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975055121250693799/10000000000000000000)
  centralHi := (509750551212506937991/100000000000000000000)
  directionLo := (512195412007249766147/100000000000000000000)
  directionHi := (128048853001812441537/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree106.table
  base := (85885991909115681711837928183954020397583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-301026663031090254702153178478534986000000000000)
      constant := (8417811931192659577831531811092943206493009875583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree106.table
  base := (85885991889771538133554887747881057585839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2715546698780728621643503160334229374000000000000)
      constant := (76102390110665136438890969731141634147953159638551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512195412007249766147/100000000000000000000)
  centralHi := (128048853001812441537/25000000000000000000)
  directionLo := (12865716451608369751/2500000000000000000)
  directionHi := (514628658064334790041/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree107.table
  base := (44193991818187905621060284576204598289747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-151932941077921199215921984136381738000000000000)
      constant := (4290015592810276537825012089940024434935962591747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree107.table
  base := (44193991809926910364642460300839533442281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1370579584185243845951228646288442017000000000000)
      constant := (38784423743215745603477003385051835402362102894529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12865716451608369751/2500000000000000000)
  centralHi := (514628658064334790041/100000000000000000000)
  directionLo := (517050453361100628999/100000000000000000000)
  directionHi := (517050453361100629/100000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree108.table
  base := (5682696701005232852276408985700482584533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-153352550640297271080767379033495983000000000000)
      constant := (4371901484058821827235257974231957721437286100264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree108.table
  base := (9092314720197299230652857539249637989919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-30741907088447186246237904720217096600000000000)
      constant := (878325983236254116596244096285878544126729643919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517050453361100628999/100000000000000000000)
  centralHi := (517050453361100629/100000000000000000)
  directionLo := (259730479026211600363/50000000000000000000)
  directionHi := (519460958052423200727/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree109.table
  base := (93491482647273250508822888996695324379379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-309544320405346685891225547861220456000000000000)
      constant := (8909127278680969022659599058231735888992500393379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree109.table
  base := (93491482635222582490910962982759026270973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2792384107550005832420365557062193354000000000000)
      constant := (80543863125134261147346121357781610271752465400757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259730479026211600363/50000000000000000000)
  centralHi := (519460958052423200727/100000000000000000000)
  directionLo := (104372065718862354143/20000000000000000000)
  directionHi := (130465082148577942679/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree110.table
  base := (19218597985840657901073928460233133848809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-62476707906019765924183267531089789200000000000)
      constant := (1815200823461651395610992087624320010613582242809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree110.table
  base := (19218597983782508160187853096482812012777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55188018000000000000000000000000000000000000000
      center := (551880180)
      previous := (275940090)
      next := (275940090)
      square := (5000643105556751387113401102793716000000000000)
      linear := (-563599315427952980535863937860969602800000000000)
      constant := (16410484277605324381761939539193562541025876652993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104372065718862354143/20000000000000000000)
  centralHi := (130465082148577942679/25000000000000000000)
  directionLo := (262124358931206894693/50000000000000000000)
  directionHi := (524248717862413789387/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree111.table
  base := (49363834530660358533496836921634918892193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-157611379327425486675303563724838718000000000000)
      constant := (4622216741998905818569684288485401155333382630193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree111.table
  base := (19745533810506676548504931623426449650537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-63191312149544977176406084923277837200000000000)
      constant := (1857222517331686534629721115614786943254996092537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262124358931206894693/50000000000000000000)
  centralHi := (524248717862413789387/100000000000000000000)
  directionLo := (526626275265682517739/100000000000000000000)
  directionHi := (26331313763284125887/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree112.table
  base := (101395520043229099187354760307663144999321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-318061977779603117080297917243905926000000000000)
      constant := (9414415378748417532852950343754272542231063185321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree112.table
  base := (25348880008931495684862256518091979993667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1434610758159641521598613976895078667000000000000)
      constant := (42555819400411083940773543015859401461546134282006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526626275265682517739/100000000000000000000)
  centralHi := (26331313763284125887/5000000000000000000)
  directionLo := (52899314685544660067/10000000000000000000)
  directionHi := (528993146855446600671/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree113.table
  base := (20819308574932467013330018682628151182487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-64180239380871052161997741407626883200000000000)
      constant := (1917189960311851759975481905695805688503656324487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree113.table
  base := (104096542868256132959991815699743948178747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2894833985909042113456182086032811994000000000000)
      constant := (86662297950708980645422237740269682855739878326723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52899314685544660067/10000000000000000000)
  centralHi := (528993146855446600671/100000000000000000000)
  directionLo := (531349475430106897163/100000000000000000000)
  directionHi := (132837368857526724291/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree114.table
  base := (53415368777731226870285318802738803096101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-161870208014553702269839748416181453000000000000)
      constant := (4879518376214925549539101831913390205031448762101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree114.table
  base := (106830737549993124501542778770384929728769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-324494050610977909301681802030607406000000000000)
      constant := (9802998969953636174147544223910914478933335482769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531349475430106897163/100000000000000000000)
  centralHi := (132837368857526724291/25000000000000000000)
  directionLo := (13342385015891823599/2500000000000000000)
  directionHi := (533695400635672943961/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree115.table
  base := (109598104085560918901355568067429000472527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-326579635153859548269370286626591396000000000000)
      constant := (9933676231359984298067201753147031391627768254527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree115.table
  base := (109598104080891723301957352695141657489441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-2946058925088560253974090350518121314000000000000)
      constant := (89805717137442154458146143237118398763038552358969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13342385015891823599/2500000000000000000)
  centralHi := (533695400635672943961/100000000000000000000)
  directionLo := (268015529531169672857/50000000000000000000)
  directionHi := (107206211812467869143/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree116.table
  base := (4495945698598515827329780641929912488863/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1226400400000000000000000000000000000000000000
      center := (12264004)
      previous := (6132002)
      next := (6132002)
      square := (111125402345705586380297802284304800000000000)
      linear := (-13176754171144467679962443056832795440000000000)
      constant := (404394729533986969326045905603584877860766446863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree116.table
  base := (14049830307622126367198163763544971163373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1485835697339159662116522241380387987000000000000)
      constant := (45699238587143979709560251609625137726747420129428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268015529531169672857/50000000000000000000)
  centralHi := (107206211812467869143/20000000000000000000)
  directionLo := (134589146084322771861/25000000000000000000)
  directionHi := (107671316867458217489/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree117.table
  base := (57616176346867009034692513956394317399317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-166129036701681917864375933107524188000000000000)
      constant := (5143806386699561069094002842478371311415623321317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree117.table
  base := (57616176345165821493797835108760861425883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-166515770237115466360666589722412813000000000000)
      constant := (5166959491117912291613692671673683565892618703883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134589146084322771861/25000000000000000000)
  centralHi := (107671316867458217489/20000000000000000000)
  directionLo := (6758401340173952461/1250000000000000000)
  directionHi := (540672107213916196881/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree118.table
  base := (59049617385994633622042333479639746057653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-167548646264057989729221328004638433000000000000)
      constant := (5233454918254340272801922030564161920052510155653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree118.table
  base := (59049617384542573643684042675871548079131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1511448166928918732375476373623042647000000000000)
      constant := (47313049067474557070089627247266485591539473526179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6758401340173952461/1250000000000000000)
  centralHi := (540672107213916196881/100000000000000000000)
  directionLo := (135744438914398573013/25000000000000000000)
  directionHi := (542977755657594292053/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree119.table
  base := (24199857739976726345940576375162928932737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (1922584815669646823188543292116000000000000)
      linear := (-233866098029666521237462592251560800000000000)
      constant := (7368691645452473806479726893177516463047406833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree119.table
  base := (60499644348702471588736993102898635266239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (43258158352567053521742224072610000000000000)
      linear := (-5274236684165391929082883874547993000000000000)
      constant := (166541451658776224677005821031496071593855765959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135744438914398573013/25000000000000000000)
  centralHi := (542977755657594292053/100000000000000000000)
  directionLo := (272636827464110142381/50000000000000000000)
  directionHi := (545273654928220284763/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree120.table
  base := (123932514477604271253059557542327382643641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-340775730777620266917824235597733846000000000000)
      constant := (10830161546910128284375679077358065317512785949641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree120.table
  base := (30983128618872203119635194828525329404197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-170784515168741978070492278429521923000000000000)
      constant := (5439436311755472778431957073149941236957194812394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272636827464110142381/50000000000000000000)
  centralHi := (545273654928220284763/100000000000000000000)
  directionLo := (273779963829806914273/50000000000000000000)
  directionHi := (547559927659613828547/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree121.table
  base := (25379782421072789890031118908754358396041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6132002000000000000000000000000000000000000000
      center := (61320020)
      previous := (30660010)
      next := (30660010)
      square := (555627011728527931901489011421524000000000000)
      linear := (-68722989980474482129503005078392467200000000000)
      constant := (2202823238840648756232401521694471147546620102041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree121.table
  base := (126898912103558594818161673477486423630549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-3099733742627114675527815143974049274000000000000)
      constant := (99572781793432792030257206428004624795039181780941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273779963829806914273/50000000000000000000)
  centralHi := (547559927659613828547/100000000000000000000)
  directionLo := (274918346967978479649/50000000000000000000)
  directionHi := (549836693935956959299/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree122.table
  base := (64949240791697768489102409505493417482277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-173227084513562277188602907593095413000000000000)
      constant := (5599811684779442561195039601057680469494078764277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree122.table
  base := (129898481581854915311075762843386138932851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-3125346212216873745786769276216703934000000000000)
      constant := (101249743604282143730337038486677905686188340889659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274918346967978479649/50000000000000000000)
  centralHi := (549836693935956959299/100000000000000000000)
  directionLo := (552104071365394739801/100000000000000000000)
  directionHi := (276052035682697369901/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree123.table
  base := (33232805727986854351134802066419411841699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-174646694075938349053448302490209658000000000000)
      constant := (5693341536488906926162858634043703094627121951398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree123.table
  base := (132931222910632782465778843196676537545933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-350106520200736979560635934273262066000000000000)
      constant := (11437859893794844646565914784229868598792368123933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552104071365394739801/100000000000000000000)
  centralHi := (276052035682697369901/50000000000000000000)
  directionLo := (554362175150926551087/100000000000000000000)
  directionHi := (34647635946932909443/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree124.table
  base := (33999284022819913565905149142581952644963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-176066303638314420918293697387323903000000000000)
      constant := (5787647652230413663012822662349550205782818405926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree124.table
  base := (135997136090157919417707592461371220688621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2759400900)
      previous := (1379700450)
      next := (1379700450)
      square := (25003215527783756935567005513968580000000000000)
      linear := (-3176571151396391886304677540702013254000000000000)
      constant := (104645768113054498663116538051742692532022794071589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554362175150926551087/100000000000000000000)
  centralHi := (34647635946932909443/6250000000000000000)
  directionLo := (139152779539677235359/25000000000000000000)
  directionHi := (556611118158708941437/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree125.table
  base := (139096221121660799659297670640633603292859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (306600100)
      previous := (153300050)
      next := (153300050)
      square := (2778135058642639659507445057107620000000000000)
      linear := (-354971826401380985566278184568876296000000000000)
      constant := (11765460064008748924508815549269455112079508986859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree125.table
  base := (6954811056035185644748917376083890878037/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27594009000000000000000000000000000000000000000
      center := (275940090)
      previous := (137970045)
      next := (137970045)
      square := (2500321552778375693556700551396858000000000000)
      linear := (-320218362098615095656363167294466791400000000000)
      constant := (10636483081099237809824307622072938839287141760666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139152779539677235359/25000000000000000000)
  centralHi := (556611118158708941437/100000000000000000000)
  directionLo := (139712752745971154531/25000000000000000000)
  directionHi := (894161617574215389/160000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree126.table
  base := (71114239001682621683356951493561409347149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-178905522763066564647984487181552393000000000000)
      constant := (5978588675811209963550103801829610507619768181149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree126.table
  base := (14222847800254868231795640200804422447487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3066001000000000000000000000000000000000000000
      center := (30660010)
      previous := (15330005)
      next := (15330005)
      square := (277813505864263965950744505710762000000000000)
      linear := (-35864401006399000298028731168748028600000000000)
      constant := (1201088079310832506576278691786168076628417589487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139712752745971154531/25000000000000000000)
  centralHi := (894161617574215389/160000000000000000)
  directionLo := (140270490503511555033/25000000000000000000)
  directionHi := (561081962014046220133/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree127.table
  base := (72696953368335508543115082135139950086951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-180325132325442636512829882078666638000000000000)
      constant := (6075223583651346389635579808837157042481541852951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree127.table
  base := (72696953367987193316935240607963269147561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1626704280082834548540769968714988617000000000000)
      constant := (54922528547004955242053208071340625619527220562049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140270490503511555033/25000000000000000000)
  centralHi := (561081962014046220133/100000000000000000000)
  directionLo := (28165203874521895821/5000000000000000000)
  directionHi := (563304077490437916421/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree128.table
  base := (74296253660928990883617466556846639134111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-181744741887818708377675276975780883000000000000)
      constant := (6172634755525212767486178808081567536431823460111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree128.table
  base := (74296253660631849663513744946564748099613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 137970045000000000000000000000000000000000000000
      center := (1379700450)
      previous := (689850225)
      next := (689850225)
      square := (12501607763891878467783502756984290000000000000)
      linear := (-1639510514877714083670247034836315947000000000000)
      constant := (55803110339552569194219451977440414034143454018517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell078.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28165203874521895821/5000000000000000000)
  centralHi := (563304077490437916421/100000000000000000000)
  directionLo := (113103492313398522101/20000000000000000000)
  directionHi := (282758730783496305253/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree129.table
  base := (2372254371237599017657405277673824365233/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-183164351450194780242520671872895128000000000000)
      constant := (6270822191433238643413290661148722965559119783456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree129.table
  base := (75912139879349696445433177185999728754331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15330005000000000000000000000000000000000000000
      center := (153300050)
      previous := (76650025)
      next := (76650025)
      square := (1389067529321319829753722528553810000000000000)
      linear := (-183590749963621513199969344550849253000000000000)
      constant := (6298967660737134007310636215084386656360507600331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell078.Kernel129
