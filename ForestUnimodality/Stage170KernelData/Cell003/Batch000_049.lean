import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell003.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_35.Batch000_049

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree000.table
  base := (9498161674833569185116743913/10000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (461582097007878083827492320000000000000)
      constant := (37992646699334276740466975652000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree000.table
  base := (9498161674833569185116743913/10000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (4038843348818933233490557800000000000000)
      constant := (332435658619174921479086036955000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree001.table
  base := (409591525473034178062918983903829162627551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (285320065357367383396258718000000000000)
      constant := (32767228675072438589350115743426583010204080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree001.table
  base := (509656818173077841286522987015947167570153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (17167395447750358507266187674000000000000)
      constant := (1997848885042893632900023319090649096874999760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1102657790843584099/4000000000000000000)
  directionHi := (6891611192772400619/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree002.table
  base := (3532532793522250855516509662844314145408163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (109058033706856682965025116000000000000)
      constant := (28260119688145328160440379173395513163265304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree002.table
  base := (1400166551932183184553170773868192494897959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (6062887453768184380098470748000000000000)
      constant := (1715195197170694129464687603949160606249999775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1102657790843584099/4000000000000000000)
  centralHi := (6891611192772400619/25000000000000000000)
  directionLo := (7796968012336761079/20000000000000000000)
  directionHi := (9746210015420951349/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree003.table
  base := (609318574523327290022294301120558620695153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-67203997943654017466208486000000000000)
      constant := (24372595089145942516866886563384594827806120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree003.table
  base := (1202054727648387609771950002992334348715379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-5041620540213989747069246178000000000000)
      constant := (1472508081117298521961239341583075377176339275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/20000000000000000000)
  centralHi := (9746210015420951349/25000000000000000000)
  directionLo := (4774648292756860073/10000000000000000000)
  directionHi := (47746482927568600731/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree004.table
  base := (5254901402474828151364251418166810507613201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-243466029594164717897442088000000000000)
      constant := (21019496551865605748774040647551242030452804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree004.table
  base := (2579884649870852165675576988827091662353007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-16146128534196163874236963104000000000000)
      constant := (1264137242323907971048527480383934114552973430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4774648292756860073/10000000000000000000)
  centralHi := (47746482927568600731/100000000000000000000)
  directionLo := (55132889542179204951/100000000000000000000)
  directionHi := (6891611192772400619/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree005.table
  base := (4531848596810998146546753359910441843025051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-419728061244675418328675690000000000000)
      constant := (18127368228471640584521076679248017372100204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree005.table
  base := (2214758674328759708794072385710862716093669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-27250636528178338001404680030000000000000)
      constant := (1085231093892362115326831378782527730885897810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/100000000000000000000)
  centralHi := (6891611192772400619/12500000000000000000)
  directionLo := (15410111101537495139/25000000000000000000)
  directionHi := (61640444406149980557/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree006.table
  base := (3908208153839590540901477726509524454500783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-595990092895186118759909292000000000000)
      constant := (15632933421355277644632110218767097818003132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree006.table
  base := (3802535787254012537242414190832303900419343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-38355144522160512128572396956000000000000)
      constant := (931629046377495116065715526448017655602739035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15410111101537495139/25000000000000000000)
  centralHi := (61640444406149980557/100000000000000000000)
  directionLo := (4220232731986434701/6250000000000000000)
  directionHi := (67523723711782955217/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree007.table
  base := (842580222964691007627368646416638006099109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-772252124545696819191142894000000000000)
      constant := (13481555403709151713431341536918458097585744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree007.table
  base := (163211465877008381363441582843566943932911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-7065664645163240893677159126000000000000)
      constant := (114250750253072576831303275931690260753037700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4220232731986434701/6250000000000000000)
  centralHi := (67523723711782955217/100000000000000000000)
  directionLo := (72933957394499943593/100000000000000000000)
  directionHi := (36466978697249971797/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree008.table
  base := (2906382029192530318294673249394066341019293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-948514156196207519622376496000000000000)
      constant := (11626015048829309602614487881752265364077172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree008.table
  base := (560408625256759681121093722320656183100123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-60564160510124860382907830808000000000000)
      constant := (686533780832515241481881097309760624297650675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72933957394499943593/100000000000000000000)
  centralHi := (36466978697249971797/50000000000000000000)
  directionLo := (7796968012336761079/10000000000000000000)
  directionHi := (77969680123367610791/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree009.table
  base := (2506226146339394755184889120566468594677911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-1124776187846718220053610098000000000000)
      constant := (10025650678709772715892810864766124378711644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree009.table
  base := (601303536732501780318546738284174267549513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-71668668504107034510075547734000000000000)
      constant := (589327682254566778064346188848402982198522740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/10000000000000000000)
  centralHi := (77969680123367610791/100000000000000000000)
  directionLo := (41349667156634403713/50000000000000000000)
  directionHi := (82699334313268807427/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree010.table
  base := (2161084861649615343256025516903771885458651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-1301038219497228920484843700000000000000)
      constant := (8645388766751573061569923756840087541834604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree010.table
  base := (412900163264371009833330647050985453096963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-82773176498089208637243264660000000000000)
      constant := (505872773064212659914976511814677180043779675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41349667156634403713/50000000000000000000)
  centralHi := (82699334313268807427/100000000000000000000)
  directionLo := (43586376234941041661/50000000000000000000)
  directionHi := (87172752469882083323/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree011.table
  base := (372678984959752370966558831472272338681969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-1477300251147739620916077302000000000000)
      constant := (7454976311656989728944673433795696773639380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree011.table
  base := (885984036638830558187015004357730408094003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-93877684492071382764410981586000000000000)
      constant := (434224963271941024171106891144168099966061470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43586376234941041661/50000000000000000000)
  centralHi := (87172752469882083323/100000000000000000000)
  directionLo := (91427554109758761193/100000000000000000000)
  directionHi := (45713777054879380597/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree012.table
  base := (401658159304537235795876614639124516084109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-1653562282798250321347310904000000000000)
      constant := (6428318519151281331090305562101992257345744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree012.table
  base := (1520802705541241844307372360363712546462403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-104982192486053556891578698512000000000000)
      constant := (372715015874986918578445823114002373883288735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91427554109758761193/100000000000000000000)
  centralHi := (45713777054879380597/50000000000000000000)
  directionLo := (95492965855137201461/100000000000000000000)
  directionHi := (47746482927568600731/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree013.table
  base := (277034201310911140442001775178202699941921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-1829824314448761021778544506000000000000)
      constant := (5542907419821564243614205963366303998838420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree013.table
  base := (652577389801458389796653420948865636147777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-116086700480035731018746415438000000000000)
      constant := (319909697163478632060516812890201961712410730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/100000000000000000000)
  centralHi := (47746482927568600731/50000000000000000000)
  directionLo := (99392230104409734567/100000000000000000000)
  directionHi := (12424028763051216821/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree014.table
  base := (238831304171655743024155644220565088363683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2006086346099271722209778108000000000000)
      constant := (4779328965869024799350281884540301767273660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree014.table
  base := (560000737956913474716609314852163449146279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-18170172639145415020844876052000000000000)
      constant := (39225488049706530897379889812505041440239530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99392230104409734567/100000000000000000000)
  centralHi := (12424028763051216821/12500000000000000000)
  directionLo := (6446511981552706427/6250000000000000000)
  directionHi := (103144191704843302833/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree015.table
  base := (1029402850862842823661491170179661721997433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2182348377749782422641011710000000000000)
      constant := (4120837840227762365281240029574896887989732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree015.table
  base := (480515083321700459197040435345903459780959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-138295716468000079273081849290000000000000)
      constant := (235664579609898169560781491498537695292669910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/6250000000000000000)
  centralHi := (103144191704843302833/100000000000000000000)
  directionLo := (106764381512576558771/100000000000000000000)
  directionHi := (26691095378144139693/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree016.table
  base := (177459831291914178498929880095990059368567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2358610409400293123072245312000000000000)
      constant := (3552990682463068400057087107903801187371340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree016.table
  base := (164907603626670105076159894492650381664063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-149400224461982253400249566216000000000000)
      constant := (202260992703055392429585548685963917538477175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764381512576558771/100000000000000000000)
  centralHi := (26691095378144139693/25000000000000000000)
  directionLo := (55132889542179204951/50000000000000000000)
  directionHi := (110265779084358409903/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree017.table
  base := (191182747958666575054358966075536998445503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2534872441050803823503478914000000000000)
      constant := (3063329709319756418066554928720841975128048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree017.table
  base := (353672891721037769636408839715470962215987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-160504732455964427527417283142000000000000)
      constant := (173588740126725328263534995130822571485833630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/50000000000000000000)
  centralHi := (110265779084358409903/100000000000000000000)
  directionLo := (113659363513958082779/100000000000000000000)
  directionHi := (5682968175697904139/5000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree018.table
  base := (659012078827787702204961715012968018104879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2711134472701314523934712516000000000000)
      constant := (2641109808156461040810088105492872072419516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree018.table
  base := (303361889952930769531069625426462799317473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-171609240449946601654585000068000000000000)
      constant := (148979049628297943915670751851335571665561770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113659363513958082779/100000000000000000000)
  centralHi := (5682968175697904139/5000000000000000000)
  directionLo := (23390904037010283237/20000000000000000000)
  directionHi := (58477260092525708093/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree019.table
  base := (4542603644612787629437369873045528956657/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-2887396504351825224365946118000000000000)
      constant := (2277063131523835689177463764293014478328500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree019.table
  base := (260164164902023357749720817178552310696103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-182713748443928775781752716994000000000000)
      constant := (127857720166211096119908793516338832241090470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23390904037010283237/20000000000000000000)
  centralHi := (58477260092525708093/50000000000000000000)
  directionLo := (24031869397974958561/20000000000000000000)
  directionHi := (60079673494937396403/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree020.table
  base := (9783454249771493672691744216755088432489/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3063658536002335924797179720000000000000)
      constant := (1963196041051784879140773061851017686497800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree020.table
  base := (223073592726741087652643390598114107218067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-193818256437910949908920433920000000000000)
      constant := (109731751058093306022786798182755912536852830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24031869397974958561/20000000000000000000)
  centralHi := (60079673494937396403/50000000000000000000)
  directionLo := (15410111101537495139/12500000000000000000)
  directionHi := (123280888812299961113/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree021.table
  base := (421330204450672041961706958179984313309069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3239920567652846625228413322000000000000)
      constant := (1692613956288131210268005250350187253236276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree021.table
  base := (76490533793776308670262698293713157821199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-29274680633127589148012592978000000000000)
      constant := (13453980174578487388265181696380402618709825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15410111101537495139/12500000000000000000)
  centralHi := (123280888812299961113/100000000000000000000)
  directionLo := (126325319804337716951/100000000000000000000)
  directionHi := (15790664975542214619/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree022.table
  base := (362811280787798184238747926815993424335833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3416182599303357325659646924000000000000)
      constant := (1459370274532505304870030132424973697343332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree022.table
  base := (327761436339285380164427162443813655107261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-216027272425875298163255867772000000000000)
      constant := (80832631375394350534209036923135145501278945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126325319804337716951/100000000000000000000)
  centralHi := (15790664975542214619/12500000000000000000)
  directionLo := (12929808699662084439/10000000000000000000)
  directionHi := (129298086996620844391/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree023.table
  base := (156166853067337124477428754054583106006531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3592444630953868026090880526000000000000)
      constant := (1258336054323791716903437273528914848052248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree023.table
  base := (280799929544436858422560568838900651690339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-227131780419857472290423584698000000000000)
      constant := (69384039803165199777938623133820459664133055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12929808699662084439/10000000000000000000)
  centralHi := (129298086996620844391/100000000000000000000)
  directionLo := (132204024818850600581/100000000000000000000)
  directionHi := (66102012409425300291/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree024.table
  base := (13439577948186563438857664616738031282893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3768706662604378726522114128000000000000)
      constant := (1085087609551714577036697034763042502631440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree024.table
  base := (24047471274352230043171094895764862826921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-238236288413839646417591301624000000000000)
      constant := (59564194724362608414014353891155113925956450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132204024818850600581/100000000000000000000)
  centralHi := (66102012409425300291/50000000000000000000)
  directionLo := (4220232731986434701/3125000000000000000)
  directionHi := (135047447423565910433/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree025.table
  base := (57807748123390425189507344673772287904439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-3944968694254889426953347730000000000000)
      constant := (935809553090643713479385812936606606471024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree025.table
  base := (51461750546233344737945240744810628139729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-249340796407821820544759018550000000000000)
      constant := (51143094119842536268612380939039415576934420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4220232731986434701/3125000000000000000)
  centralHi := (135047447423565910433/100000000000000000000)
  directionLo := (137832223855448012377/100000000000000000000)
  directionHi := (68916111927724006189/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree026.table
  base := (39765865445668952307352168366520241335631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-4121230725905400127384581332000000000000)
      constant := (807211166957295992788603906619404826712620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree026.table
  base := (176110797049063476762313095954246891449921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-260445304401803994671926735476000000000000)
      constant := (43923267788801362122720613114861688405230645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137832223855448012377/100000000000000000000)
  centralHi := (68916111927724006189/50000000000000000000)
  directionLo := (35140459952040917893/25000000000000000000)
  directionHi := (140561839808163671573/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree027.table
  base := (42719254323900693138154799673303170604323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-4297492757555910827815814934000000000000)
      constant := (696454267661760700721437383595100729669168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree027.table
  base := (9410881388374032269384728716947059808931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-271549812395786168799094452402000000000000)
      constant := (37735176926366706975816886757802274451009520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35140459952040917893/25000000000000000000)
  centralHi := (140561839808163671573/100000000000000000000)
  directionLo := (143239448782705802191/100000000000000000000)
  directionHi := (8952465548919112637/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree028.table
  base := (146762095651395971675336378811132377191721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-4473754789206421528247048536000000000000)
      constant := (601090987028278788756813962000529508766884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree028.table
  base := (128642805873507544205031694232692354994889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-40379188627109763275180309904000000000000)
      constant := (4633323448574611035326192405718632424821115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143239448782705802191/100000000000000000000)
  centralHi := (8952465548919112637/6250000000000000000)
  directionLo := (145867914788999887187/100000000000000000000)
  directionHi := (36466978697249971797/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree029.table
  base := (12595675748376265191892179134327205501563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-4650016820856932228678282138000000000000)
      constant := (519010105809003428950771278463338220062520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree029.table
  base := (109806836711025880999828130777728223165041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-293758828383750517053429886254000000000000)
      constant := (27892561957199436472577291343567614675435045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145867914788999887187/100000000000000000000)
  centralHi := (36466978697249971797/25000000000000000000)
  directionLo := (148449848239088696243/100000000000000000000)
  directionHi := (37112462059772174061/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree030.table
  base := (108005787953293621690626054166714931500291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-4826278852507442929109515740000000000000)
      constant := (448390764646297854932311804491859726001164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree030.table
  base := (46814139188458286002311401721537954738723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-304863336377732691180597603180000000000000)
      constant := (24005780872240560752667789680933597821974270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148449848239088696243/100000000000000000000)
  centralHi := (37112462059772174061/25000000000000000000)
  directionLo := (37746909078365276277/25000000000000000000)
  directionHi := (150987636313461105109/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree031.table
  base := (46258290393891973321688022540650774609451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5002540884157953629540749342000000000000)
      constant := (387662538451342329313143051285456196875608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree031.table
  base := (79731164565523252080999289817876696012657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-315967844371714865307765320106000000000000)
      constant := (20680809140259840628642818361467990523100965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37746909078365276277/25000000000000000000)
  centralHi := (150987636313461105109/100000000000000000000)
  directionLo := (76741734403197345023/50000000000000000000)
  directionHi := (153483468806394690047/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree032.table
  base := (39575264539502601743862325869885658487493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5178802915808464329971982944000000000000)
      constant := (335470999591223158935476569455085267899944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree032.table
  base := (67792717099028312978921029096373089336547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-327072352365697039434933037032000000000000)
      constant := (17838566107691962079243419987760206887454015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76741734403197345023/50000000000000000000)
  centralHi := (153483468806394690047/100000000000000000000)
  directionLo := (7796968012336761079/5000000000000000000)
  directionHi := (155939360246735221581/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree033.table
  base := (16903899918905920350454826829453549872861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5355064947458975030403216546000000000000)
      constant := (290648015460605500511902091703506797965776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree033.table
  base := (57535823009387182036974816490104271952463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-338176860359679213562100753958000000000000)
      constant := (15411159097366004802423359386637346628353435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/5000000000000000000)
  centralHi := (155939360246735221581/100000000000000000000)
  directionLo := (39589292232463722109/25000000000000000000)
  directionHi := (158357168929854888437/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree034.table
  base := (57659928484386995791775320103604061306963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5531326979109485730834450148000000000000)
      constant := (252186129686479815666880851183416245227852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree034.table
  base := (4872257544699035050116577370046831640931/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-349281368353661387689268470884000000000000)
      constant := (13340300931127639153453891374941937520280950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39589292232463722109/25000000000000000000)
  centralHi := (158357168929854888437/100000000000000000000)
  directionLo := (160738613372133242743/100000000000000000000)
  directionHi := (20092326671516655343/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree035.table
  base := (49066296348899658571653127357221266021597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5707589010759996431265683750000000000000)
      constant := (219216465643264152056654596935135064086388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree035.table
  base := (41148728006540242840435057853651264090851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-51483696621091937402348026830000000000000)
      constant := (1653707319954137018175085635512794243179785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160738613372133242743/100000000000000000000)
  centralHi := (20092326671516655343/12500000000000000000)
  directionLo := (81542643301087660111/50000000000000000000)
  directionHi := (163085286602175320223/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree036.table
  base := (41647364460734355998077631758881156259901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-5883851042410507131696917352000000000000)
      constant := (190989668097249254707722939679524625039604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree036.table
  base := (34638933322720088058461377134551860171963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-371490384341625735943603904736000000000000)
      constant := (10075149918517355829639767112880405742130935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81542643301087660111/50000000000000000000)
  centralHi := (163085286602175320223/100000000000000000000)
  directionLo := (165398668626537614853/100000000000000000000)
  directionHi := (82699334313268807427/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree037.table
  base := (17620782446618117663545311561286693786141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6060113074061017832128150954000000000000)
      constant := (166859465341815712644253038672543550289128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree037.table
  base := (29042655045155654379548971400264224234971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-382594892335607910070771621662000000000000)
      constant := (8801015561801142475650933132802534937567895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165398668626537614853/100000000000000000000)
  centralHi := (82699334313268807427/50000000000000000000)
  directionLo := (167680137347119117797/100000000000000000000)
  directionHi := (83840068673559558899/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree038.table
  base := (29709556198179541558325772079429649777033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6236375105711528532559384556000000000000)
      constant := (146268491584060505864779576438718599108132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree038.table
  base := (24230657978613600227323666186932407223831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-393699400329590084197939338588000000000000)
      constant := (7721885546698150379047424764711239769838595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167680137347119117797/100000000000000000000)
  centralHi := (83840068673559558899/50000000000000000000)
  directionLo := (10620686134935979131/6250000000000000000)
  directionHi := (169930978158975666097/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree039.table
  base := (24931166383443837104222315831727729333147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6412637137362039232990618158000000000000)
      constant := (128736058855501884019059501787160917332588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree039.table
  base := (20091994635020411851215562070184058925243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-404803908323572258325107055514000000000000)
      constant := (6810577738630368670939616649635294436684535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10620686134935979131/6250000000000000000)
  centralHi := (169930978158975666097/100000000000000000000)
  directionLo := (43038098104603639469/25000000000000000000)
  directionHi := (172152392418414557877/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree040.table
  base := (10401378133488329112057768723864598954319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6588899169012549933421851760000000000000)
      constant := (113847610427929992144433946990916791634552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree040.table
  base := (8265709000935921033223263382064502503649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-415908416317554432452274772440000000000000)
      constant := (6043756619534256791056866377531606226788010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43038098104603639469/25000000000000000000)
  centralHi := (172152392418414557877/100000000000000000000)
  directionLo := (34869100987952833329/20000000000000000000)
  directionHi := (87172752469882083323/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree041.table
  base := (8617472706090149963232896985566891456857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6765161200663060633853085362000000000000)
      constant := (101245624554954010274744340224785131654856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree041.table
  base := (6733580127916657468061448968174640352519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-427012924311536606579442489366000000000000)
      constant := (5401389072692843634860226676957773772734310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/20000000000000000000)
  centralHi := (87172752469882083323/50000000000000000000)
  directionLo := (176511370653617849919/100000000000000000000)
  directionHi := (551598033292555781/312500000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree042.table
  base := (7075325397042361128286439345489708430071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-6941423232313571334284318964000000000000)
      constant := (90621769136693778591189854644917667440568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree042.table
  base := (1082902567170810096859301948036666822717/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-62588204615074111529515743756000000000000)
      constant := (695182449347561496699291685975233387950950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176511370653617849919/100000000000000000000)
  centralHi := (551598033292555781/312500000000000000)
  directionLo := (89325490269206468549/50000000000000000000)
  directionHi := (178650980538412937099/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree043.table
  base := (11483395198139094333562202473479453714871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7117685263964082034715552566000000000000)
      constant := (81710135314945973570272133716167814859484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree043.table
  base := (1711350658748870155387550226651682917423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-449221940299500954833777923218000000000000)
      constant := (4423656903595314217366122387722111573843175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89325490269206468549/50000000000000000000)
  centralHi := (178650980538412937099/100000000000000000000)
  directionLo := (22595658364998300629/12500000000000000000)
  directionHi := (180765266919986405033/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree044.table
  base := (573490516511070050009347279396380812931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7293947295614592735146786168000000000000)
      constant := (74281401649045413782854342045368372027584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree044.table
  base := (6598611218717669446645487924527741612747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-460326448293483128960945640144000000000000)
      constant := (4060854030890018102218125216872496695123015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22595658364998300629/12500000000000000000)
  centralHi := (180765266919986405033/100000000000000000000)
  directionLo := (182855108219517522387/100000000000000000000)
  directionHi := (45713777054879380597/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree045.table
  base := (1794642046621389381545616893594595609997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7470209327265103435578019770000000000000)
      constant := (68137800916139122708326587203763529759952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree045.table
  base := (2455094867278168933617459199528825900537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-471430956287465303088113357070000000000000)
      constant := (3766988147859470949383128982774124691263130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182855108219517522387/100000000000000000000)
  centralHi := (45713777054879380597/25000000000000000000)
  directionLo := (184921333218449941669/100000000000000000000)
  directionHi := (18492133321844994167/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree046.table
  base := (2724458239277244640650868879646856029673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7646471358915614136009253372000000000000)
      constant := (63108779170187439425252077086174848237384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree046.table
  base := (215835324375302675448652615546217850791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-482535464281447477215281073996000000000000)
      constant := (3532718959946072017136871511940373975100720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184921333218449941669/100000000000000000000)
  centralHi := (18492133321844994167/10000000000000000000)
  directionLo := (93482362449563889843/50000000000000000000)
  directionHi := (186964724899127779687/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree047.table
  base := (3950122004300517118817275576467362890091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7822733390566124836440486974000000000000)
      constant := (59047251866856768146870445898119451560364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree047.table
  base := (1097705223870239656380893653342244248021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-493639972275429651342448790922000000000000)
      constant := (3350028318505758591819356417483499681530290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93482362449563889843/50000000000000000000)
  centralHi := (186964724899127779687/100000000000000000000)
  directionLo := (11811626494476358809/6250000000000000000)
  directionHi := (37797204782324348189/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree048.table
  base := (331309218673746079381759199564290171953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-7998995422216635536871720576000000000000)
      constant := (55826374948812419258481663922057285502496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree048.table
  base := (1108231188025840883050341429962531775969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-504744480269411825469616507848000000000000)
      constant := (3212033115202866080701603430385620285112405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11811626494476358809/6250000000000000000)
  centralHi := (37797204782324348189/20000000000000000000)
  directionLo := (95492965855137201461/50000000000000000000)
  directionHi := (190985931710274402923/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree049.table
  base := (1522624628397066947298496624861594742293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-8175257453867146237302954178000000000000)
      constant := (53336760074351285229231190379696378969172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree049.table
  base := (167710261874095073034127639993104325007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-73692712609056285656683460682000000000000)
      constant := (444689235505088647822309755556358651375245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel049
