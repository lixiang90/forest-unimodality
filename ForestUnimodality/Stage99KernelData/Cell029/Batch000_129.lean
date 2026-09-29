import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell029.Parameters
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch000_049
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch050_099
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch100_149
import ForestUnimodality.BinomialMassData.Q22_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_47.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree000.table
  base := (470363681263855542458074407977/10000000000000000000000000000)
  polynomial :=
    { denominator := 17390000000000000000000000000000000000000000
      center := (95115)
      previous := (82263)
      next := (0)
      square := (2239467364778108718903482038600000000000000)
      linear := (10078264817343921700976139225300000000000000)
      constant := (817962441717844788334591395472003000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree000.table
  base := (470363681263855542458074407977/10000000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (1275)
      previous := (1122)
      next := (0)
      square := (30263072497001469174371378900000000000000)
      linear := (136192767801944887851028908450000000000000)
      constant := (11053546509700605247764748587459500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree001.table
  base := (283869188971595668283881344964588440740301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (13913841657973990474406189584534900000000000000)
      constant := (851164288279415448725677334233741859999999800421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree001.table
  base := (282143049339909392932469410244167221648869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (10138969793646690170652036051100000000000000)
      constant := (617884804722980602053460325359165392622351621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24934291273026982011/50000000000000000000)
  directionHi := (49868582546053964023/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree002.table
  base := (178751957472149546325508767177355939042907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (10301580798586901110814873056273100000000000000)
      constant := (527661840162788442924549600747904519734374959747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree002.table
  base := (44204973919670511992695341641701329652639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (3737909706955280441653677353950000000000000)
      constant := (190551674022631403180444087604436474405359102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/50000000000000000000)
  centralHi := (49868582546053964023/100000000000000000000)
  directionLo := (70524825772951726743/100000000000000000000)
  directionHi := (8815603221618965843/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree003.table
  base := (1846886818310321373510324127460752539267/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (6689319939199811747223556528011300000000000000)
      constant := (340607726928155852417654268756285259507242195648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree003.table
  base := (116545682134998029450702789924103671856099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (4812669034174431595962673364700000000000000)
      constant := (245081581116010875039992677941345011130122691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/100000000000000000000)
  centralHi := (8815603221618965843/12500000000000000000)
  directionLo := (86374918671207987321/100000000000000000000)
  directionHi := (43187459335603993661/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree004.table
  base := (82208414446013735489614122513067867095881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (3077059079812722383632239999749500000000000000)
      constant := (229497841924261334154359183900165911309862745601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree004.table
  base := (40455541316623874186299772585802831497683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (1074759327219151154308996010750000000000000)
      constant := (82367651317101612995291014511238454778381747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/100000000000000000000)
  centralHi := (43187459335603993661/50000000000000000000)
  directionLo := (24934291273026982011/25000000000000000000)
  directionHi := (19947433018421585609/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree005.table
  base := (59886364240947047211364131113188159012911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-535201779574366979959076528512300000000000000)
      constant := (161403839654569101380567768702377188622283426231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree005.table
  base := (58894912286233596464652630434765312282399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-513631725297826978726689321700000000000000)
      constant := (115718715184020342540208053311396574831819391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/25000000000000000000)
  centralHi := (19947433018421585609/20000000000000000000)
  directionLo := (22301908102907240079/20000000000000000000)
  directionHi := (27877385128634050099/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree006.table
  base := (9059917349531811548193334129229547451749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-4147462638961456343550393056774100000000000000)
      constant := (118377504498558694246668264608317641346653188145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree006.table
  base := (44535666837250658488344050584834254335263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-3176782105033956266071370664900000000000000)
      constant := (84862855862401066926984499568698867826595967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/20000000000000000000)
  centralHi := (27877385128634050099/25000000000000000000)
  directionLo := (122152581433695409089/100000000000000000000)
  directionHi := (12215258143369540909/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree007.table
  base := (35193466411838017102538155717228190152879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-7759723498348545707141709585035900000000000000)
      constant := (90576485211509309103841627470526031633314594359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree007.table
  base := (34588424407796124854822858236943260149061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-5839932484770085553416052008100000000000000)
      constant := (64999692239732692769139625021207661669275749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/100000000000000000000)
  centralHi := (12215258143369540909/10000000000000000000)
  directionLo := (131939867652155034383/100000000000000000000)
  directionHi := (8246241728259689649/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree008.table
  base := (27769851717295320997878729137238173671377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-11371984357735635070733026113297700000000000000)
      constant := (72562954032133147733211406966167843001258284617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree008.table
  base := (27272953680414924043128007919943128434891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-8503082864506214840760733351300000000000000)
      constant := (52196693335756967076870480223154370712674219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/100000000000000000000)
  centralHi := (8246241728259689649/6250000000000000000)
  directionLo := (70524825772951726743/50000000000000000000)
  directionHi := (141049651545903453487/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree009.table
  base := (5505931555061976411710343146087297471201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-14984245217122724434324342641559500000000000000)
      constant := (61297619627440527512895621900816756463623357284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree009.table
  base := (21600563443885412913323180127140902936233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-11166233244242344128105414694500000000000000)
      constant := (44269840264885280154057735384254254586138697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/50000000000000000000)
  centralHi := (141049651545903453487/100000000000000000000)
  directionLo := (149605747638161892067/100000000000000000000)
  directionHi := (37401436909540473017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree010.table
  base := (4345886168369404353304177947655649856211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-18596506076509813797915659169821300000000000000)
      constant := (55052060012868838450407143153939905995258662124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree010.table
  base := (1063247671409285086254977403536389317317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-6914691811989236707725048018850000000000000)
      constant := (19991829653033417271105105896295072015626024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/100000000000000000000)
  centralHi := (37401436909540473017/25000000000000000000)
  directionLo := (157698304529649210199/100000000000000000000)
  directionHi := (788491522648246051/500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree011.table
  base := (211187778263664555304386014634670919901/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-22208766935896903161506975698083100000000000000)
      constant := (52818368113652226778097607854492202045563649344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree011.table
  base := (13182222557633875492776694034167335034121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-16492534003714602702794777380900000000000000)
      constant := (38620382256837609104406807725275643090373289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/100000000000000000000)
  centralHi := (788491522648246051/500000000000000000)
  directionLo := (82697688566063590233/50000000000000000000)
  directionHi := (165395377132127180467/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree012.table
  base := (10219973144044366898624351976050472553881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-25821027795283992525098292226344900000000000000)
      constant := (53988174001160016659875431773493931110115163601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree012.table
  base := (4957770333830543604223381538158302125879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-9577842191725365995069729362050000000000000)
      constant := (19873741004973845866866065302191689396066711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82697688566063590233/50000000000000000000)
  centralHi := (165395377132127180467/100000000000000000000)
  directionLo := (86374918671207987321/50000000000000000000)
  directionHi := (172749837342415974643/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree013.table
  base := (294739538640213010739040698750364775161/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-29433288654671081888689608754606700000000000000)
      constant := (58177649545747479474308706572018796855616462025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree013.table
  base := (7088293434945513174102943673433592877711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-21818834763186861277484140067300000000000000)
      constant := (43091873949751616903438114111614806666863599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/50000000000000000000)
  centralHi := (172749837342415974643/100000000000000000000)
  directionLo := (44950932851126526141/25000000000000000000)
  directionHi := (35960746280901220913/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree014.table
  base := (4877206849474409089291018777801206264277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-33045549514058171252280925282868500000000000000)
      constant := (65131689198170871358024782849350061689131625517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree014.table
  base := (92361482294243725280945866423416644881/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-12240992571461495282414410705250000000000000)
      constant := (24235760788520741116429001627433184213553225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/25000000000000000000)
  centralHi := (35960746280901220913/20000000000000000000)
  directionLo := (186591150251388859511/100000000000000000000)
  directionHi := (23323893781423607439/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree015.table
  base := (67171757041613550828630422680726609237/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-36657810373445260615872241811130300000000000000)
      constant := (74671089557542526259145385460923465370096227080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree015.table
  base := (48934722590701301921148066531237251327/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-13572567761329559926086751376850000000000000)
      constant := (27878989551141581154331248615687577204533575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186591150251388859511/100000000000000000000)
  centralHi := (23323893781423607439/12500000000000000000)
  directionLo := (38628037939967373347/20000000000000000000)
  directionHi := (12071261856239804171/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree016.table
  base := (753591168115861427817881922812385558819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-40270071232832349979463558339392100000000000000)
      constant := (86663129227816889813491688377304514228521273099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree016.table
  base := (265500584583335755201299956941776421299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-14904142951197624569759092048450000000000000)
      constant := (32427822369069988938003268835284384114649491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38628037939967373347/20000000000000000000)
  centralHi := (12071261856239804171/6250000000000000000)
  directionLo := (199474330184215856089/100000000000000000000)
  directionHi := (19947433018421585609/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree017.table
  base := (-239162825008804861322450376777115639943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-43882332092219439343054874867653900000000000000)
      constant := (101004925166472603290027923578899349095279739588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree017.table
  base := (-581415921795893575629267199386565411589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-16235718141065689213431432720050000000000000)
      constant := (37845036402539897976306966677455077005799899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199474330184215856089/100000000000000000000)
  centralHi := (19947433018421585609/10000000000000000000)
  directionLo := (25701679154651722091/12500000000000000000)
  directionHi := (205613433237213776729/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree018.table
  base := (-1235598062641097874821142288221976224483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-47494592951606528706646191395915700000000000000)
      constant := (117613800921950035601522811456728238076080491114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree018.table
  base := (-532388423586618274057966220668483227117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-35134586661867507714207546783300000000000000)
      constant := (88201224429995764455151980518716602756492735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/12500000000000000000)
  centralHi := (205613433237213776729/100000000000000000000)
  directionLo := (211574477318855180229/100000000000000000000)
  directionHi := (21157447731885518023/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree019.table
  base := (-3812602799458090193471103516507649403891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-51106853810993618070237507924177500000000000000)
      constant := (136421533861247614282536490431414970777055745189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree019.table
  base := (-797762554948647960655550060917559616821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-37797737041603637001552228126500000000000000)
      constant := (102339434398850712351221188790565554032212055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/100000000000000000000)
  centralHi := (21157447731885518023/10000000000000000000)
  directionLo := (54343027943966374067/25000000000000000000)
  directionHi := (217372111775865496269/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree020.table
  base := (-2499917673140594682186759436705906951159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-54719114670380707433828824452439300000000000000)
      constant := (157370774481994370779497745342989991929908187522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree020.table
  base := (-322648201701263331172887846715043168321/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-20230443710669883144448454734850000000000000)
      constant := (59031446027945149973194026574851757129431288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/25000000000000000000)
  centralHi := (217372111775865496269/100000000000000000000)
  directionLo := (22301908102907240079/10000000000000000000)
  directionHi := (223019081029072400791/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree021.table
  base := (-1209807368476348338403942114206675425933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-58331375529767796797420140980701100000000000000)
      constant := (180412704167148161581023962009878672521260350535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree021.table
  base := (-1549684950605613846017245673174972488779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-21562018900537947788120795406450000000000000)
      constant := (67667991590321212744408210314812971544574378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/10000000000000000000)
  centralHi := (223019081029072400791/100000000000000000000)
  directionLo := (22852655431744591741/10000000000000000000)
  directionHi := (228526554317445917411/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree022.table
  base := (-3487032162476437972527245294459160787831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-61943636389154886161011457508962900000000000000)
      constant := (205505417559535464922152222983684436438287456898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree022.table
  base := (-888969790143652784599641131950157888273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-22893594090406012431793136078050000000000000)
      constant := (77064067804480765996901743855488404899219772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22852655431744591741/10000000000000000000)
  centralHi := (228526554317445917411/100000000000000000000)
  directionLo := (233904385494067120827/100000000000000000000)
  directionHi := (58476096373516780207/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree023.table
  base := (-7786878480269941823341909889353811176957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-65555897248541975524602774037224700000000000000)
      constant := (232612744096616583993179954604284463189729620203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree023.table
  base := (-197834200950197852159326518141991433139/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-24225169280274077075465476749650000000000000)
      constant := (87206485554709936309817568625986818483918980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233904385494067120827/100000000000000000000)
  centralHi := (58476096373516780207/25000000000000000000)
  directionLo := (239161320197288080191/100000000000000000000)
  directionHi := (3736895628082626253/1562500000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree024.table
  base := (-531115081703155220272357058373736152217/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-69168158107929064888194090565486500000000000000)
      constant := (261703347839862996118092611054599738457941979888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree024.table
  base := (-8613907161703899581194412264197696639163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-51113488940284283438275634842500000000000000)
      constant := (196167652578987287756920994506787288124088933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239161320197288080191/100000000000000000000)
  centralHi := (3736895628082626253/1562500000000000000)
  directionLo := (122152581433695409089/50000000000000000000)
  directionHi := (244305162867390818179/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree025.table
  base := (-4557976182711569855718971763431153804981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-72780418967316154251785407093748300000000000000)
      constant := (292750013032313395013683732209834131448254106598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree025.table
  base := (-1152793354056425597891134173106533120173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-26888319660010206362810158092850000000000000)
      constant := (109686181384465276061677445548930673350151372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/50000000000000000000)
  centralHi := (244305162867390818179/100000000000000000000)
  directionLo := (249342912730269820111/100000000000000000000)
  directionHi := (15583932045641863757/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree026.table
  base := (-9649041745423409146146782175965785234783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-76392679826703243615376723622010100000000000000)
      constant := (325729060532445065529633086948061873590002799257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree026.table
  base := (-9746484710296087047257726818291588753763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-56439789699756542012964997528900000000000000)
      constant := (244009876648208808621563598873193880442937533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249342912730269820111/100000000000000000000)
  centralHi := (15583932045641863757/6250000000000000000)
  directionLo := (254280875517541722929/100000000000000000000)
  directionHi := (25428087551754172293/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree027.table
  base := (-10103930936197461195264508883043829784643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-80004940686090332978968040150271900000000000000)
      constant := (360619861332284629014303728130099810427835626197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree027.table
  base := (-10193106806606881022974990534195155279643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-59102940079492671300309678872100000000000000)
      constant := (270065203917708080611034406737762901987268613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254280875517541722929/100000000000000000000)
  centralHi := (25428087551754172293/10000000000000000000)
  directionLo := (64781189003405990491/25000000000000000000)
  directionHi := (51824951202724792393/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree028.table
  base := (-655410550565141935080244157202243349111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-83617201545477422342559356678533700000000000000)
      constant := (397404425325216605823770078738991314253489497104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree028.table
  base := (-5284062246849666479932381256543887349043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-30883045229614400293827180107650000000000000)
      constant := (148762643177991663213218242026294552845964013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64781189003405990491/25000000000000000000)
  centralHi := (51824951202724792393/20000000000000000000)
  directionLo := (131939867652155034383/50000000000000000000)
  directionHi := (263879735304310068767/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree029.table
  base := (-5401073819429637953894164021548367306311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-87229462404864511706150673206795500000000000000)
      constant := (436067050443673785994222985806069359826542944738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree029.table
  base := (-10876691473727175628441527682955584243307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-64429240838964929874999041558500000000000000)
      constant := (326378739434976950377703333611751114406534837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/50000000000000000000)
  centralHi := (263879735304310068767/100000000000000000000)
  directionLo := (268550535708691789161/100000000000000000000)
  directionHi := (134275267854345894581/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree030.table
  base := (-2211040540089935198796966739974524806197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-90841723264251601069741989735057300000000000000)
      constant := (476594021467889089903825235131709000342793610815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree030.table
  base := (-5561652093103952009921940299743000612077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-33546195609350529581171861450850000000000000)
      constant := (178307815259897403014704900020867711647921907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268550535708691789161/100000000000000000000)
  centralHi := (134275267854345894581/50000000000000000000)
  directionLo := (273141475712821654627/100000000000000000000)
  directionHi := (68285368928205413657/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree031.table
  base := (-562484905520761190583136943998636401337/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-94453984123638690433333306263319100000000000000)
      constant := (518973350429600708902942330456054193747047004460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree031.table
  base := (-565594415468134578406018820043767776341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-34877770799218594224844202122450000000000000)
      constant := (194113643893623160632871312521133169820627310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273141475712821654627/100000000000000000000)
  centralHi := (68285368928205413657/25000000000000000000)
  directionLo := (5553130334495330027/2000000000000000000)
  directionHi := (277656516724766501351/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree032.table
  base := (-11389101013137667310619209899296315015277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-98066244983025779796924622791580900000000000000)
      constant := (563194552264673766999885715382701328539685503483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree032.table
  base := (-1144587346000264043603810346820065047169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-36209345989086658868516542794050000000000000)
      constant := (210603067606897885704574655189772381554018395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5553130334495330027/2000000000000000000)
  centralHi := (277656516724766501351/100000000000000000000)
  directionLo := (70524825772951726743/25000000000000000000)
  directionHi := (282099303091806906973/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree033.table
  base := (-5738222905514390182887651632661080307293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-101678505842412869160515939319842700000000000000)
      constant := (609248450573052368172255249585197182320057571094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree033.table
  base := (-1441032226016139279630093343416264338577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-37540921178954723512188883465650000000000000)
      constant := (227772774920955072118766378004073888304333628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/25000000000000000000)
  centralHi := (282099303091806906973/100000000000000000000)
  directionLo := (286473196529859903059/100000000000000000000)
  directionHi := (14323659826492995153/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree034.table
  base := (-2302877969431196189165729340043301127373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-105290766701799958524107255848104500000000000000)
      constant := (657127009227762129325135094418756660756938179335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree034.table
  base := (-11561664033610525058629940342094297961453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-77744992737645576311722448274500000000000000)
      constant := (491239738171760117449601852192713695803150323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286473196529859903059/100000000000000000000)
  centralHi := (14323659826492995153/5000000000000000000)
  directionLo := (5815626117803252801/2000000000000000000)
  directionHi := (290781305890162640051/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree035.table
  base := (-2876315431048853942452096719503412291991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-108903027561187047887698572376366300000000000000)
      constant := (706823186252549458966428107814352485264527540356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree035.table
  base := (-11548387828113656630601478602047265101761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-80408143117381705599067129617700000000000000)
      constant := (528283629020453765786237689215077591390209951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5815626117803252801/2000000000000000000)
  centralHi := (290781305890162640051/100000000000000000000)
  directionLo := (295026513012544233821/100000000000000000000)
  directionHi := (147513256506272116911/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree036.table
  base := (-5725551632650464400038462830600012225681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-112515288420574137251289888904628100000000000000)
      constant := (758330806927136531338830940689200320856122697198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree036.table
  base := (-11490439965504539450045264961656338635773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-83071293497117834886411810960900000000000000)
      constant := (566672780588521027879368670388501147953577443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295026513012544233821/100000000000000000000)
  centralHi := (147513256506272116911/50000000000000000000)
  directionLo := (149605747638161892067/50000000000000000000)
  directionHi := (59842299055264756827/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree037.table
  base := (-2270741195335924755068241371962409836281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4470405)
      previous := (3866361)
      next := (0)
      square := (105254966144571109788463655814200000000000000)
      linear := (-3138582412971925043645437984672700000000000000)
      constant := (21936336581621103072349767876258081784256225135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree037.table
  base := (-11389582815918665226658454300496410560573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-85734443876853964173756492304100000000000000)
      constant := (606403299800332602542273780584003429071694243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/50000000000000000000)
  centralHi := (59842299055264756827/20000000000000000000)
  directionLo := (303338745350220844891/100000000000000000000)
  directionHi := (75834686337555211223/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree038.table
  base := (-1401830343775918792015341752272731714309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-119739810139348315978472521961151700000000000000)
      constant := (866759369415729819690015990191409374363137220888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree038.table
  base := (-5623681027453254414504924842279163832989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-44198797128295046730550586823650000000000000)
      constant := (323735886129298745395142266914405327092927299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303338745350220844891/100000000000000000000)
  centralHi := (75834686337555211223/25000000000000000000)
  directionLo := (307410588555109347761/100000000000000000000)
  directionHi := (153705294277554673881/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree039.table
  base := (-2207059088385483389515733117436588052451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-123352070998735405342063838489413500000000000000)
      constant := (923671375714504003339095145827167339511169147145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree039.table
  base := (-1383141776795117181917544864658313122227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-45530372318163111374222927495250000000000000)
      constant := (344937600692182174491243382392579145252002228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307410588555109347761/100000000000000000000)
  centralHi := (153705294277554673881/50000000000000000000)
  directionLo := (155714599091536150967/50000000000000000000)
  directionHi := (62285839636614460387/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree040.table
  base := (-5408439437525443909886210937522699433047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-126964331858122494705655155017675300000000000000)
      constant := (982376798643919497914177677642877833335668946626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree040.table
  base := (-5422045316366453271611686088127113344291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-46861947508031176017895268166850000000000000)
      constant := (366805477755497508278640427275327206622461181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155714599091536150967/50000000000000000000)
  centralHi := (62285839636614460387/20000000000000000000)
  directionLo := (157698304529649210199/50000000000000000000)
  directionHi := (315396609059298420399/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree041.table
  base := (-1320057717678535033646093437843025919231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-130576592717509584069246471545937100000000000000)
      constant := (1042872406350508625137678905670613384912873832392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree041.table
  base := (-1058527828568516947869644155822009905431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-48193522697899240661567608838450000000000000)
      constant := (389338360934625235642454925271845900594514605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/50000000000000000000)
  centralHi := (315396609059298420399/100000000000000000000)
  directionLo := (319314729587058856193/100000000000000000000)
  directionHi := (159657364793529428097/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree042.table
  base := (-5133492405672266315111152650353278481061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-134188853576896673432837788074198900000000000000)
      constant := (1105155353831096527008669460496959686253150655238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree042.table
  base := (-10289617912770080275571233703347967190423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-99050195775534610610479899020100000000000000)
      constant := (825070466545459563148863781156104340476355593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319314729587058856193/100000000000000000000)
  centralHi := (159657364793529428097/50000000000000000000)
  directionLo := (323185352478123795539/100000000000000000000)
  directionHi := (16159267623906189777/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree043.table
  base := (-4968638403142574556224374055470126013881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-137801114436283762796429104602460700000000000000)
      constant := (1169223134931635739051564656533691254097552352798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree043.table
  base := (-9957919799308140078166203800520738315119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-101713346155270739897824580363300000000000000)
      constant := (872790399619349305121343178875649689061902129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323185352478123795539/100000000000000000000)
  centralHi := (16159267623906189777/5000000000000000000)
  directionLo := (327010164339828612323/100000000000000000000)
  directionHi := (81752541084957153081/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree044.table
  base := (-4786034120858588043921030784722144291271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-141413375295670852160020421130722500000000000000)
      constant := (1235073540484961541524843669945285168567474504418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree044.table
  base := (-9590897524045604288849427170836917481171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-104376496535006869185169261706500000000000000)
      constant := (921834944795469219018516965318021249284093261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327010164339828612323/100000000000000000000)
  centralHi := (81752541084957153081/25000000000000000000)
  directionLo := (330790754264254360933/100000000000000000000)
  directionHi := (165395377132127180467/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree045.table
  base := (-9172003505833868869108624603777265691913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-145025636155057941523611737658984300000000000000)
      constant := (1302704621783206558978989573382953991498506366527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree045.table
  base := (-4594589970631051681585255610302056936381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-53519823457371499236256971524850000000000000)
      constant := (486101356467357800582038028861342756227534371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330790754264254360933/100000000000000000000)
  centralHi := (165395377132127180467/50000000000000000000)
  directionLo := (167264310771804300593/50000000000000000000)
  directionHi := (334528621543608601187/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree046.table
  base := (-8532862699911725947864769726403993131/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-148637897014445030887203054187246100000000000000)
      constant := (1372114658687976331552992705625815348206015640576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree046.table
  base := (-350132865193509869236430315981610551947/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-109702797294479127759858624392900000000000000)
      constant := (1023892478972342289827633560082715557268726925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167264310771804300593/50000000000000000000)
  centralHi := (334528621543608601187/100000000000000000000)
  directionLo := (169112591309029611529/50000000000000000000)
  directionHi := (338225182618059223059/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree047.table
  base := (-4134757186811757321201316848916003808887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 643430000000000000000000000000000000000000000
      center := (3519255)
      previous := (3043731)
      next := (0)
      square := (82860292496790022599428835428200000000000000)
      linear := (-3239365061145364260655199376925700000000000000)
      constant := (30708555995195577071694155109412995133849567518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree047.table
  base := (-258869125330314639815321507335975409191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (1275)
      previous := (1122)
      next := (0)
      square := (30263072497001469174371378900000000000000)
      linear := (-1195382422066119755821311763150000000000000)
      constant := (11456416614657526938531989628183346492288368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169112591309029611529/50000000000000000000)
  centralHi := (338225182618059223059/100000000000000000000)
  directionLo := (341881777347334072347/100000000000000000000)
  directionHi := (85470444336833518087/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree048.table
  base := (-155360730555435203740433385368064896831/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-155862418733219209614385687243769700000000000000)
      constant := (1516265697983762776116679273201059110806526972450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree048.table
  base := (-7781083306067927617230832157712301041617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-115029098053951386334547987079300000000000000)
      constant := (1131233806571368358762027951203613526999068047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341881777347334072347/100000000000000000000)
  centralHi := (85470444336833518087/25000000000000000000)
  directionLo := (69099934936966389857/20000000000000000000)
  directionHi := (172749837342415974643/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree049.table
  base := (-1808402675657509497937044474510080860171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-159474679592606298977977003772031500000000000000)
      constant := (1591004169334676701617654892131432499036235261236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree049.table
  base := (-7245517494253689595108339737743479433563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-117692248433687515621892668422500000000000000)
      constant := (1186883569563794264202276264842724653931259333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69099934936966389857/20000000000000000000)
  centralHi := (172749837342415974643/50000000000000000000)
  directionLo := (87270019455594437039/25000000000000000000)
  directionHi := (349080077822377748157/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree050.table
  base := (-6666584614359675417228909845557580787073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-163086940451993388341568320300293300000000000000)
      constant := (1667516494291188389413345735894095063232616012167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree050.table
  base := (-6677452386371335070807601511202555228943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-120355398813423644909237349765700000000000000)
      constant := (1243851704530047295257997663671753555499264913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87270019455594437039/25000000000000000000)
  centralHi := (349080077822377748157/100000000000000000000)
  directionLo := (70524825772951726743/20000000000000000000)
  directionHi := (88156032216189658429/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree051.table
  base := (-6067266253451902455270855840278840890907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-166699201311380477705159636828555100000000000000)
      constant := (1745801741452785510569698455877693311406149432253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree051.table
  base := (-379824183936997842918554806309101042789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-61509274596579887098291015554450000000000000)
      constant := (651068775533112944421500331312805566371832792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/20000000000000000000)
  centralHi := (88156032216189658429/25000000000000000000)
  directionLo := (178066456542762778913/50000000000000000000)
  directionHi := (356132913085525557827/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree052.table
  base := (-5435928609911926083318313143936651471289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-170311462170767567068750953356816900000000000000)
      constant := (1825859085264660528556877226402779349615994038031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree052.table
  base := (-340311620403463393633849383677373566721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-62840849786447951741963356226050000000000000)
      constant := (680870262156160676427191519788053454328906488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178066456542762778913/50000000000000000000)
  centralHi := (356132913085525557827/100000000000000000000)
  directionLo := (44950932851126526141/12500000000000000000)
  directionHi := (359607462809012209129/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree053.table
  base := (-238640690769227023298034083427360489361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-173923723030154656432342269885078700000000000000)
      constant := (1907687793491421656801069786818026843391062466380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree053.table
  base := (-1195270993791283698995948921286783580573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-64172424976316016385635696897650000000000000)
      constant := (711330052976050229486337348110254990141028486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/12500000000000000000)
  centralHi := (359607462809012209129/100000000000000000000)
  directionLo := (90762190239482327491/25000000000000000000)
  directionHi := (72609752191585861993/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree054.table
  base := (-2039068388222980485212664566572819747161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-177535983889541745795933586413340500000000000000)
      constant := (1991287216229578724309721142629579575546791459038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree054.table
  base := (-4085689173885599496447802870158802923499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-131008000332368162058616075138500000000000000)
      constant := (1484895836326318487409536133248219204341990709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90762190239482327491/25000000000000000000)
  centralHi := (72609752191585861993/20000000000000000000)
  directionLo := (91614436075271556817/25000000000000000000)
  directionHi := (366457744301086227269/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree055.table
  base := (-670417672719856735714584055302790223691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-181148244748928835159524902941602300000000000000)
      constant := (2076656776263635037656658738526927353629706746945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree055.table
  base := (-3358986184437819847474509438570492796449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-133671150712104291345960756481700000000000000)
      constant := (1548447307517012823876465907541197781412644159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91614436075271556817/25000000000000000000)
  centralHi := (366457744301086227269/100000000000000000000)
  directionLo := (369835306431650591457/100000000000000000000)
  directionHi := (184917653215825295729/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree056.table
  base := (-259483821211218832781635178080493445399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-184760505608315924523116219469864100000000000000)
      constant := (2163795960596015265926697747982741600814065307210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree056.table
  base := (-2601138992742966851572361865714363523889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-136334301091840420633305437824900000000000000)
      constant := (1613314157279283601628922860835436970975729199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369835306431650591457/100000000000000000000)
  centralHi := (184917653215825295729/50000000000000000000)
  directionLo := (373182300502777719023/100000000000000000000)
  directionHi := (23323893781423607439/6250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree057.table
  base := (-18065371835514304040131371072217028809/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-188372766467703013886707535998125900000000000000)
      constant := (2252704313003087290953191261531215296662109811100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree057.table
  base := (-453073330212131287430276547960306811889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-69498725735788274960325059584050000000000000)
      constant := (839748031856563963547491367064011364505074398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373182300502777719023/100000000000000000000)
  centralHi := (23323893781423607439/6250000000000000000)
  directionLo := (37649954174434009457/10000000000000000000)
  directionHi := (376499541744340094571/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree058.table
  base := (-39492781221967945604616351978785009529/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-191985027327090103250298852526387700000000000000)
      constant := (2343381427488646805512855343152145617454953774775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree058.table
  base := (-248144686558120057090475216866322315737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-70830300925656339603997400255650000000000000)
      constant := (873496370290948465167548504200884588009073934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37649954174434009457/10000000000000000000)
  centralHi := (376499541744340094571/100000000000000000000)
  directionLo := (1483546131960125331/390625000000000000)
  directionHi := (379787809781792084737/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree059.table
  base := (-2746096037037337400608068072106492377/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-195597288186477192613890169054649500000000000000)
      constant := (2435826942522819376820720606754635262108318719150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree059.table
  base := (-28422113037264159583230542411599651999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-144323752231048808495339481854500000000000000)
      constant := (1815803933196082712787944795992463881843671045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1483546131960125331/390625000000000000)
  centralHi := (379787809781792084737/100000000000000000000)
  directionLo := (47880981346982136987/12500000000000000000)
  directionHi := (383047850775857095897/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree060.table
  base := (46462530003750681877429203958837140261/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-199209549045864281977481485582911300000000000000)
      constant := (2530040535968734589445235604039556240503091769296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree060.table
  base := (369504283843556765613752031718091713471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-73493451305392468891342081598850000000000000)
      constant := (942964707395833800877088801964065264595057439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47880981346982136987/12500000000000000000)
  centralHi := (383047850775857095897/100000000000000000000)
  directionLo := (386280379399673733471/100000000000000000000)
  directionHi := (12071261856239804171/3125000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree061.table
  base := (827350670313635348090486784904608885093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-202821809905251371341072802111173100000000000000)
      constant := (2626021920611833609779727698518081721452392656506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree061.table
  base := (1650687195958303088070551310516746163197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-149650052990521067070028844540900000000000000)
      constant := (1957368983341398788280559705618731492274502173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386280379399673733471/100000000000000000000)
  centralHi := (12071261856239804171/3125000000000000000)
  directionLo := (97371520167060553633/25000000000000000000)
  directionHi := (389486080668242214533/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree062.table
  base := (1298256524791716164871520126507099463781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-206434070764638460704664118639434900000000000000)
      constant := (2723770840217538239580331398397646252275017723002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree062.table
  base := (518568757904552510208506497781912436751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-152313203370257196357373525884100000000000000)
      constant := (2030122458745275464291741962566801222863914795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97371520167060553633/25000000000000000000)
  centralHi := (389486080668242214533/100000000000000000000)
  directionLo := (392665611633436879151/100000000000000000000)
  directionHi := (24541600727089804947/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree063.table
  base := (3568759970605300172882395504821032263243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-210046331624025550068255435167696700000000000000)
      constant := (2823287066052455140131538285167159884908950684403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree063.table
  base := (891351405804688700045147269151453936467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-77488176874996662822359103613650000000000000)
      constant := (1052094840176707676244863210148611123491311206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392665611633436879151/100000000000000000000)
  centralHi := (24541600727089804947/6250000000000000000)
  directionLo := (395819602956465103149/100000000000000000000)
  directionHi := (7916392059129302063/2000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree064.table
  base := (457137454552254892671126405187194980287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-213658592483412639431846751695958500000000000000)
      constant := (2924570393812502709120150560979180652709805027270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree064.table
  base := (114207694685378526177219769476614136919/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-78819752064864727466031444285250000000000000)
      constant := (1089785252390221633645473234394676812569081420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395819602956465103149/100000000000000000000)
  centralHi := (7916392059129302063/2000000000000000000)
  directionLo := (398948660368431712179/100000000000000000000)
  directionHi := (19947433018421585609/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree065.table
  base := (5604296396728883990325559745837651756887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-217270853342799728795438068224220300000000000000)
      constant := (3027620640908493821311387559926736805268688871327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree065.table
  base := (1400373078606068335130614087117857929221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-80151327254732792109703784956850000000000000)
      constant := (1128132401987868597185551303583386696331298378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398948660368431712179/100000000000000000000)
  centralHi := (19947433018421585609/5000000000000000000)
  directionLo := (50256670753573673281/12500000000000000000)
  directionHi := (402053366028589386249/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree066.table
  base := (104179242710842800230210472457630275889/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-220883114202186818159029384752482100000000000000)
      constant := (3132437644065926971096394013455858344963309988416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree066.table
  base := (3332453703319288502887531403902436806899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-81482902444600856753376125628450000000000000)
      constant := (1167136231759191000636884063086620482906439891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50256670753573673281/12500000000000000000)
  centralHi := (402053366028589386249/100000000000000000000)
  directionLo := (81026855957780188821/20000000000000000000)
  directionHi := (202567139894450472053/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree067.table
  base := (7760851649665852152311954017578366078049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-224495375061573907522620701280743900000000000000)
      constant := (3239021257201153882058201681656378306002315619929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree067.table
  base := (1939626688516784393710681232748469861067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-82814477634468921397048466300050000000000000)
      constant := (1206796690554803878969561221672182739846194006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81026855957780188821/20000000000000000000)
  centralHi := (202567139894450472053/50000000000000000000)
  directionLo := (40819194037269289287/10000000000000000000)
  directionHi := (408191940372692892871/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree068.table
  base := (1776878700362906353436891433814132618219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-228107635920960996886212017809005700000000000000)
      constant := (3347371349540809503863304524418338142737705302495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree068.table
  base := (8882248930495604173964852416287357154857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-168292105648673972081441613943300000000000000)
      constant := (2494227465238906963287028414703578771955079113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40819194037269289287/10000000000000000000)
  centralHi := (408191940372692892871/100000000000000000000)
  directionLo := (25701679154651722091/6250000000000000000)
  directionHi := (411226866474427553457/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree069.table
  base := (2509514589556348078331565367490803176593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-231719896780348086249803334337267500000000000000)
      constant := (3457487803955502391750848524848103720772806399012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree069.table
  base := (80288774870717325925702510729687825269/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-170955256028410101368786295286500000000000000)
      constant := (2576174634003000374180581193438635050752402625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/6250000000000000000)
  centralHi := (411226866474427553457/100000000000000000000)
  directionLo := (414239557786951663057/100000000000000000000)
  directionHi := (207119778893475831529/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree070.table
  base := (2244362302067817422653736934208523329297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-235332157639735175613394650865529300000000000000)
      constant := (3569370515482349345687220414113501568895584864685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree070.table
  base := (5610008668717865675119000767541469228591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-86809203204073115328065488314850000000000000)
      constant := (1329717407029706559133395102602499105525957519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414239557786951663057/100000000000000000000)
  centralHi := (207119778893475831529/50000000000000000000)
  directionLo := (83446099192396492573/20000000000000000000)
  directionHi := (208615247980991231433/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree071.table
  base := (49742487357069348797103689034670906171/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-238944418499122264976985967393791100000000000000)
      constant := (3683019390014066824592232023332934703860187672750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree071.table
  base := (12433980620035166577292046036447352382173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-176281556787882359943475657972900000000000000)
      constant := (2744007939698681962100281801862312201412220157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83446099192396492573/20000000000000000000)
  centralHi := (208615247980991231433/50000000000000000000)
  directionLo := (210100072754529562961/50000000000000000000)
  directionHi := (420200145509059125923/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree072.table
  base := (13679461430918070657481436059129583199619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-242556679358509354340577283922052900000000000000)
      constant := (3798434343135062797857649363217988214275215009899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree072.table
  base := (13677960043160338134045647815339888977433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-178944707167618489230820339316100000000000000)
      constant := (2829893952021184813748241060748885814751149497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210100072754529562961/50000000000000000000)
  centralHi := (420200145509059125923/100000000000000000000)
  directionLo := (211574477318855180229/50000000000000000000)
  directionHi := (423148954637710360459/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree073.table
  base := (1869163154256487131228808436300390442283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-246168940217896443704168600450314700000000000000)
      constant := (3915615299087358148832551839190829884357658465944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree073.table
  base := (186899146190737143989237840490260151367/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-90803928773677309259082510329650000000000000)
      constant := (1458546399103151349418582114328219386974788120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/50000000000000000000)
  centralHi := (423148954637710360459/100000000000000000000)
  directionLo := (85215471209432306567/20000000000000000000)
  directionHi := (106519339011790383209/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree074.table
  base := (16257130756281290015183431882085548287501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4470405)
      previous := (3866361)
      next := (0)
      square := (105254966144571109788463655814200000000000000)
      linear := (-6750843272359014407236754512934500000000000000)
      constant := (109042221347331119430004422954551798118182319233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree074.table
  base := (406396853069320108242978308062355104839/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-92135503963545373902754851001250000000000000)
      constant := (1502802215431562707859574456874394848531787020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85215471209432306567/20000000000000000000)
  centralHi := (106519339011790383209/25000000000000000000)
  directionLo := (428985767667520942539/100000000000000000000)
  directionHi := (21449288383376047127/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree075.table
  base := (17590917793626623741443152782637130136349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-253393461936670622431351233506838300000000000000)
      constant := (4155274954327463538099979668252941380625065874229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree075.table
  base := (3517953613766021511225244139421348300057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-186934158306826877092854383345700000000000000)
      constant := (3095428807453223315011856745134908791974129565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428985767667520942539/100000000000000000000)
  centralHi := (21449288383376047127/5000000000000000000)
  directionLo := (215937296678019968303/50000000000000000000)
  directionHi := (431874593356039936607/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree076.table
  base := (2369331023721323142065113170841603912011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-257005722796057711794942550035100100000000000000)
      constant := (4277753537609094037216639449386917656511956938648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree076.table
  base := (9476798120395258754932943997553959784837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-94798654343281503190099532344450000000000000)
      constant := (1593282944888576916663701791782996697164704933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215937296678019968303/50000000000000000000)
  centralHi := (431874593356039936607/100000000000000000000)
  directionLo := (54343027943966374067/12500000000000000000)
  directionHi := (434744223551730992537/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree077.table
  base := (2543538202701770970144319955957235823839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-260617983655444801158533866563361900000000000000)
      constant := (4401997890333116425808035160922791515654590564152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree077.table
  base := (4069468620664891212049601018781056223211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-192260459066299135667543746032100000000000000)
      constant := (3279015643517373932575094933810236765985365495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/12500000000000000000)
  centralHi := (434744223551730992537/100000000000000000000)
  directionLo := (218797517945673946507/50000000000000000000)
  directionHi := (87519007178269578603/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree078.table
  base := (21771875408141873130818898947962590040069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-264230244514831890522125183091623700000000000000)
      constant := (4528007968102363433581645920076737075754563504349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree078.table
  base := (10885497347053308208227727753632081873019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-97461804723017632477444213687650000000000000)
      constant := (1686389018915553505027007892774773268857498971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218797517945673946507/50000000000000000000)
  centralHi := (87519007178269578603/20000000000000000000)
  directionLo := (110106848947369825029/25000000000000000000)
  directionHi := (440427395789479300117/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree079.table
  base := (23225344339958220670660687899788414123753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-267842505374218979885716499619885500000000000000)
      constant := (4655783730970024790425965985854870638708338046113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree079.table
  base := (11612269229775422344179546151721416920299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-98793379912885697121116554359250000000000000)
      constant := (1733926522493740625910435426605852609976940491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110106848947369825029/25000000000000000000)
  centralHi := (440427395789479300117/100000000000000000000)
  directionLo := (17729666279411138281/4000000000000000000)
  directionHi := (221620828492639228513/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree080.table
  base := (988348021086742466135416958549880287117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-271454766233606069249307816148147300000000000000)
      constant := (4785325142979620401337160779943274563093913728925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree080.table
  base := (6176990777079645356315850634035758659363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-100124955102753761764788895030850000000000000)
      constant := (1782120320021964890024536874349169981757065734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17729666279411138281/4000000000000000000)
  centralHi := (221620828492639228513/50000000000000000000)
  directionLo := (446038162058144801581/100000000000000000000)
  directionHi := (223019081029072400791/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree081.table
  base := (26221933263550036320996838984407933634869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-275067027092993158612899132676409100000000000000)
      constant := (4916632171754236885441018869891480404671813675149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree081.table
  base := (3277657310075042201711303127236632691639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-101456530292621826408461235702450000000000000)
      constant := (1830970400278716716753925827873162886463322204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446038162058144801581/100000000000000000000)
  centralHi := (223019081029072400791/50000000000000000000)
  directionLo := (448817242914485676201/100000000000000000000)
  directionHi := (224408621457242838101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree082.table
  base := (27765032905198118301968713442604148517629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-278679287952380247976490449204670900000000000000)
      constant := (5049704788129540042542354013200965200219280729109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree082.table
  base := (27764415431404240955450014149901327099313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-205576210964979782104267152748100000000000000)
      constant := (3760953506326705166290502542727932031562382417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448817242914485676201/100000000000000000000)
  centralHi := (224408621457242838101/50000000000000000000)
  directionLo := (451579221247516038739/100000000000000000000)
  directionHi := (22578961062375801937/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree083.table
  base := (29337990762044742988561636526541118857479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-282291548811767337340081765732932700000000000000)
      constant := (5184542965825712547031544695108154054900398250959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree083.table
  base := (7334356431572912797805174007471383744701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-104119680672357955695805917045650000000000000)
      constant := (1930639369580935011032092636896508573384089018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451579221247516038739/100000000000000000000)
  centralHi := (22578961062375801937/5000000000000000000)
  directionLo := (454324408971899328481/100000000000000000000)
  directionHi := (227162204485949664241/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree084.table
  base := (3867599875103645184295268013745837485637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-285903809671154426703673082261194500000000000000)
      constant := (5321146681154026069664978924066101206423216400616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree084.table
  base := (7735070487045204362430046295072341228077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-105451255862226020339478257717250000000000000)
      constant := (1981458241339297206577118640160829603545644186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454324408971899328481/100000000000000000000)
  centralHi := (227162204485949664241/50000000000000000000)
  directionLo := (457053108634891834821/100000000000000000000)
  directionHi := (228526554317445917411/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree085.table
  base := (32573450558265573468016641638427959186399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-289516070530541516067264398789456300000000000000)
      constant := (5459515912754249692779768176357199898362732130279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree085.table
  base := (32572977413998676900764262157629199867971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-213565662104188169966301196777700000000000000)
      constant := (4065866722113969943768781621563202902508347939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457053108634891834821/100000000000000000000)
  centralHi := (228526554317445917411/50000000000000000000)
  directionLo := (459765613805524646221/100000000000000000000)
  directionHi := (229882806902762323111/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree086.table
  base := (34235939063295037558766629687932037421171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-293128331389928605430855715317718100000000000000)
      constant := (5599650641359530279417868047944865420938149065691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree086.table
  base := (34235506100100906608011835635438907966747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-216228812483924299253645878120900000000000000)
      constant := (4170129444161766304541440826777484547698544123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459765613805524646221/100000000000000000000)
  centralHi := (229882806902762323111/50000000000000000000)
  directionLo := (231231104721620136763/50000000000000000000)
  directionHi := (462462209443240273527/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree087.table
  base := (35928258767435547037466723511424822960513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-296740592249315694794447031845979900000000000000)
      constant := (5741550849585762674968011088762451747036169534073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree087.table
  base := (17963931287751810469690535127883521023843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-109445981431830214270495279732050000000000000)
      constant := (2137852318412470046055473060829394697941669187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231231104721620136763/50000000000000000000)
  centralHi := (462462209443240273527/100000000000000000000)
  directionLo := (23257158612364711613/5000000000000000000)
  directionHi := (465143172247294232261/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree088.table
  base := (2353150280147224867064434208249770693383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-300352853108702784158038348374241700000000000000)
      constant := (5885216521742804623128205546657514076784705461488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree088.table
  base := (9412510485519682654779373994929203994567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-110777556621698278914167620403650000000000000)
      constant := (2191296144641763178633577940945597223247997006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23257158612364711613/5000000000000000000)
  centralHi := (465143172247294232261/100000000000000000000)
  directionLo := (93561754197626848331/20000000000000000000)
  directionHi := (58476096373516780207/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree089.table
  base := (985059288097372459662284370549770094757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-303965113968089873521629664902503500000000000000)
      constant := (6030647643665188618465959257296135751549065343880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree089.table
  base := (19701019890480378070865985426755520125361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-112109131811566343557839961075250000000000000)
      constant := (2245396195888125627891222296449402943956922449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93561754197626848331/20000000000000000000)
  centralHi := (58476096373516780207/12500000000000000000)
  directionLo := (235229633410940184739/50000000000000000000)
  directionHi := (470459266821880369479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree090.table
  base := (20592077830921340420754053947371162853861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-307577374827476962885220981430765300000000000000)
      constant := (6177844202560245443843684271736570556761561962362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree090.table
  base := (41183852104497396606455271281190668169671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-226881414002868816403024603493700000000000000)
      constant := (4600304935494390854967013039758150185986803239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235229633410940184739/50000000000000000000)
  centralHi := (470459266821880369479/100000000000000000000)
  directionLo := (473094913588947630597/100000000000000000000)
  directionHi := (236547456794473815299/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree091.table
  base := (21497876537430387133681659708886469042027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-311189635686864052248812297959027100000000000000)
      constant := (6326806186871786088327242423873122115291687466534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree091.table
  base := (1074886882828769331213484751908077513027/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-114772282191302472845184642418450000000000000)
      constant := (2355564956243282990314766437297198864525532860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473094913588947630597/100000000000000000000)
  centralHi := (236547456794473815299/50000000000000000000)
  directionLo := (475715958097777526643/100000000000000000000)
  directionHi := (118928989524444381661/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree092.table
  base := (44837160310006409800315803372484415215721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-314801896546251141612403614487288900000000000000)
      constant := (6477533586157693812797647794019621142226581406241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree092.table
  base := (44836906156822198800212651354418515446853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-232207714762341074977713966180100000000000000)
      constant := (4823267315573308632595496465378710500622098277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475715958097777526643/100000000000000000000)
  centralHi := (118928989524444381661/25000000000000000000)
  directionLo := (478322640394576160383/100000000000000000000)
  directionHi := (3736895628082626253/781250000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree093.table
  base := (11677093561592431419990161304848176069827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-318414157405638230975994931015550700000000000000)
      constant := (6630026390979959565198162911614008584257845188268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree093.table
  base := (4670814170013162135459347383587523156603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-117435432571038602132529323761650000000000000)
      constant := (2468358569135182138101301199532224193264680135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478322640394576160383/100000000000000000000)
  centralHi := (3736895628082626253/781250000000000000)
  directionLo := (120228798504973325829/25000000000000000000)
  directionHi := (480915194019893303317/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree094.table
  base := (48609392062394056113323138502507903746643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 643430000000000000000000000000000000000000000
      center := (3519255)
      previous := (3043731)
      next := (0)
      square := (82860292496790022599428835428200000000000000)
      linear := (-6851625920532453624246515905187500000000000000)
      constant := (144346480697996905953495134348806166050770250549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree094.table
  base := (48609179291234474644117297599452210068827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2550)
      previous := (2244)
      next := (0)
      square := (60526144994002938348742757800000000000000)
      linear := (-5053915223868368798987304869500000000000000)
      constant := (107478284568506558820548948144374253873234869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120228798504973325829/25000000000000000000)
  centralHi := (480915194019893303317/100000000000000000000)
  directionLo := (241746923126409314031/50000000000000000000)
  directionHi := (483493846252818628063/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree095.table
  base := (404321689651953178997322274768306329201/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-325638679124412409703177564072074300000000000000)
      constant := (6940308183919076307563640479461006663071207165125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree095.table
  base := (25270008266902170316908261454607497904267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-120098582950774731419874005104850000000000000)
      constant := (2583777009814077770122923764362727962870525803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241746923126409314031/50000000000000000000)
  centralHi := (483493846252818628063/100000000000000000000)
  directionLo := (486058818343517779417/100000000000000000000)
  directionHi := (243029409171758889709/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree096.table
  base := (52500829370629165022830390151202576643779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-329250939983799499066768880600336100000000000000)
      constant := (7098097157339829992155245188436840087282561593259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree096.table
  base := (10500130252370059994417086555549215023341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-242860316281285592127092691552900000000000000)
      constant := (5284941068210732162395046268058841079932801345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486058818343517779417/100000000000000000000)
  centralHi := (243029409171758889709/50000000000000000000)
  directionLo := (488610325734781636357/100000000000000000000)
  directionHi := (244305162867390818179/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree097.table
  base := (54491244466524368655970925774998698954511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-332863200843186588430360197128597900000000000000)
      constant := (7257651506752920137370309886617804540481014759831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree097.table
  base := (13622770379268432186618284052662873464901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-122761733330510860707218686448050000000000000)
      constant := (2701820258070828235395396381289564574967932618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488610325734781636357/100000000000000000000)
  centralHi := (244305162867390818179/50000000000000000000)
  directionLo := (767419653551900999/156250000000000000)
  directionHi := (491148578273216639361/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree098.table
  base := (56511454604268188503425598014798081369063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-336475461702573677793951513656859700000000000000)
      constant := (7418971226443025476922412573342673688627892168623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree098.table
  base := (14127826382125284409635105344007876977881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-124093308520378925350891027119650000000000000)
      constant := (2761826179754424013764327396674826800488278258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (767419653551900999/156250000000000000)
  centralHi := (491148578273216639361/100000000000000000000)
  directionLo := (493673780410662087201/100000000000000000000)
  directionHi := (246836890205331043601/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree099.table
  base := (29280729036520313571699993574494441249673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-340087722561960767157542830185121500000000000000)
      constant := (7582056311236419329388358886248507008332804724866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree099.table
  base := (29280660847078958503624967912803188132413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-125424883710246989994563367791250000000000000)
      constant := (2822488297386772459955790424406082242584500317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493673780410662087201/100000000000000000000)
  centralHi := (246836890205331043601/50000000000000000000)
  directionLo := (2480930656981907707/500000000000000000)
  directionHi := (496186131396381541401/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree100.table
  base := (60641253323754856472870101130376077654573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-343699983421347856521134146713383300000000000000)
      constant := (7746906756448475687078403807481549034332824955333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree100.table
  base := (60641128564572965699957937709463958871843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-253512917800230109276471416925700000000000000)
      constant := (5767613218733865485493380903220205885147901187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2480930656981907707/500000000000000000)
  centralHi := (496186131396381541401/100000000000000000000)
  directionLo := (498685825460539640223/100000000000000000000)
  directionHi := (15583932045641863757/3125000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree101.table
  base := (245120464661784999508866430291667345119/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-347312244280734945884725463241645100000000000000)
      constant := (7913522557836371183877116622915427939907485542144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree101.table
  base := (1568768120698162721671243485710829397221/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-128088034089983119281908049134450000000000000)
      constant := (2945781114245999920815407155833604442769223780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498685825460539640223/100000000000000000000)
  centralHi := (15583932045641863757/3125000000000000000)
  directionLo := (250586525994721234599/50000000000000000000)
  directionHi := (501173051989442469199/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree102.table
  base := (4055638355689332019087061230317998204493/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-350924505140122035248316779769906900000000000000)
      constant := (8081903711556455210944235911058114620770713210448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree102.table
  base := (12978021859334654563277514952600791260331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-258839218559702367851160779612100000000000000)
      constant := (6016823621424660478739274148574275739470355895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250586525994721234599/50000000000000000000)
  centralHi := (501173051989442469199/100000000000000000000)
  directionLo := (503647995692988936363/100000000000000000000)
  directionHi := (125911998923247234091/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree103.table
  base := (13411875276976277449576357580338146366381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-354536765999509124611908096298168700000000000000)
      constant := (8252050214125815779114538861140191877638232380505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree103.table
  base := (67059280895490866329123050161651875625061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-261502368939438497138505460955300000000000000)
      constant := (6143397395156460234614998912586088993255759749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503647995692988936363/100000000000000000000)
  centralHi := (125911998923247234091/25000000000000000000)
  directionLo := (253055418382376076843/50000000000000000000)
  directionHi := (506110836764752153687/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree104.table
  base := (13851665198217616986951853157224783868327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-358149026858896213975499412826430500000000000000)
      constant := (8423962062387618036595615326733398453083344577835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree104.table
  base := (69258238650418967267354256664419022116387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-264165519319174626425850142298500000000000000)
      constant := (6271283547535920757655805086810101619855098883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253055418382376076843/50000000000000000000)
  centralHi := (506110836764752153687/100000000000000000000)
  directionLo := (254280875517541722929/50000000000000000000)
  directionHi := (508561751035083445859/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree105.table
  base := (35743530781625108275833052205555755169743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-361761287718283303339090729354692300000000000000)
      constant := (8597639253479836322110996220165271451759356741806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree105.table
  base := (1787174541976723762547720503947598981741/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-133414334849455377856597411820850000000000000)
      constant := (3200241038306922787475675448414904923013317380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254280875517541722929/50000000000000000000)
  centralHi := (508561751035083445859/100000000000000000000)
  directionLo := (102200182023521425111/20000000000000000000)
  directionHi := (127750227529401781389/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree106.table
  base := (3687279112156237653973520956532722674179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-365373548577670392702682045882954100000000000000)
      constant := (8773081784807039868500315407308267576523217433180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree106.table
  base := (73745509181796111821097939998811488732617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-269491820078646885000539504984900000000000000)
      constant := (6530992980623819534898015782024174578610350953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102200182023521425111/20000000000000000000)
  centralHi := (127750227529401781389/25000000000000000000)
  directionLo := (64178560193681429597/12500000000000000000)
  directionHi := (513428481549451436777/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree107.table
  base := (76033887252204030682789547549908961143103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-368985809437057482066273362411215900000000000000)
      constant := (8950289654014927300898051635778229437481041787463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree107.table
  base := (19008455108434453365683972041520678990151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-136077485229191507143942093164050000000000000)
      constant := (3331408128982310535339565734597338359778487118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64178560193681429597/12500000000000000000)
  centralHi := (513428481549451436777/100000000000000000000)
  directionLo := (515844628925539935681/100000000000000000000)
  directionHi := (257922314462769967841/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree108.table
  base := (244849924637854537864426093102450584431/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-372598070296444571429864678939477700000000000000)
      constant := (9129262858967336365909036668725933308428819248320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree108.table
  base := (612124334200241023918873192715258770323/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-137409060419059571787614433835650000000000000)
      constant := (3397975953592177881925977962547312423913184448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515844628925539935681/100000000000000000000)
  centralHi := (257922314462769967841/50000000000000000000)
  directionLo := (64781189003405990491/12500000000000000000)
  directionHi := (518249512027247923929/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree109.table
  base := (5043740468609154536118428646254400066229/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-376210331155831660793455995467739500000000000000)
      constant := (9310001397725483298156908090601219141322952155344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree109.table
  base := (80699791617330252388062823038453319730843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-277481271217855272862573549014500000000000000)
      constant := (6930399926966139370761137608275343383285432187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64781189003405990491/12500000000000000000)
  centralHi := (518249512027247923929/100000000000000000000)
  directionLo := (520643286945710257103/100000000000000000000)
  directionHi := (32540205434106891069/6250000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree110.table
  base := (83077501511063929991537196528094748630857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-379822592015218750157047311996001300000000000000)
      constant := (9492505268529211244787989076740063919324295901697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree110.table
  base := (83077450411959683070162507666502636751619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-280144421597591402149918230357700000000000000)
      constant := (7066160316115176068779117291897304324584326371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520643286945710257103/100000000000000000000)
  centralHi := (32540205434106891069/6250000000000000000)
  directionLo := (261513053100024907093/50000000000000000000)
  directionHi := (523026106200049814187/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree111.table
  base := (5342808587218261323742924541668226261621/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4470405)
      previous := (3866361)
      next := (0)
      square := (105254966144571109788463655814200000000000000)
      linear := (-10363104131746103770828071041196300000000000000)
      constant := (261534445129190528416816801565033306192657107088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree111.table
  base := (85484890670630757755863909223482576694247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-282807571977327531437262911700900000000000000)
      constant := (7203233073547093414663214508418473011917591623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261513053100024907093/50000000000000000000)
  centralHi := (523026106200049814187/100000000000000000000)
  directionLo := (262699059425390018249/50000000000000000000)
  directionHi := (525398118850780036499/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree112.table
  base := (87922154670861131744242266091191902171263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-387047113733992928884229945052524900000000000000)
      constant := (9862809000025905752016510616102704546386062034823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree112.table
  base := (8792211194767492913710884881143086584607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-142735361178531830362303796522050000000000000)
      constant := (3670809099138704793704964370326625391326984315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262699059425390018249/50000000000000000000)
  centralHi := (525398118850780036499/100000000000000000000)
  directionLo := (131939867652155034383/25000000000000000000)
  directionHi := (527759470608620137533/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree113.table
  base := (45194576450414591501954878792304940759553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-390659374593380018247821261580786700000000000000)
      constant := (10050608857947230054826997357100350519509440355826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree113.table
  base := (90389113838337333653367014430262731512203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-288133872736799790011952274387300000000000000)
      constant := (7481315689412021093414048529393450373910456427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/25000000000000000000)
  centralHi := (527759470608620137533/100000000000000000000)
  directionLo := (530110303938947767423/100000000000000000000)
  directionHi := (4141486749523029433/781250000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree114.table
  base := (92885931688747438682998307920827158214039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-394271635452767107611412578109048500000000000000)
      constant := (10240174042344508202998938237393321846525397834719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree114.table
  base := (46442947987443541983035739738569089051797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-145398511558267959649648477865250000000000000)
      constant := (3811162773069305201272339766886699117715419573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530110303938947767423/100000000000000000000)
  centralHi := (4141486749523029433/781250000000000000)
  directionLo := (266225379081050506691/50000000000000000000)
  directionHi := (532450758162101013383/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree115.table
  base := (95412490673920283494211289731830137482839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-397883896312154196975003894637310300000000000000)
      constant := (10431504552126953011734098492928833887194740559519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree115.table
  base := (95412458023103078717623979937339694620641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-293460173496272048586641637073700000000000000)
      constant := (7764647767718883101902887188584583385416995969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266225379081050506691/50000000000000000000)
  centralHi := (532450758162101013383/100000000000000000000)
  directionLo := (267390484774864780987/50000000000000000000)
  directionHi := (21391238781989182479/4000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree116.table
  base := (19593765905644744841854523896883134337193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-401496157171541286338595211165572100000000000000)
      constant := (10624600386302277822506990625696372805474632161765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree116.table
  base := (97968799679098506709723410040683616041651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-296123323876008177873986318416900000000000000)
      constant := (7908282353481553225551624351180670107836007059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267390484774864780987/50000000000000000000)
  centralHi := (21391238781989182479/4000000000000000000)
  directionLo := (268550535708691789161/50000000000000000000)
  directionHi := (537101071417383578323/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree117.table
  base := (20110989590609344708034148348396991044381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-405108418030928375702186527693833900000000000000)
      constant := (10819461543967446726623155842657455984770622570505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree117.table
  base := (100554920666450906132869219495587325676089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-298786474255744307161330999760100000000000000)
      constant := (8053229302816003555353704305967552402418480601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268550535708691789161/50000000000000000000)
  centralHi := (537101071417383578323/100000000000000000000)
  directionLo := (134852798553379578423/25000000000000000000)
  directionHi := (539411194213518313693/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree118.table
  base := (20634169135304840940553336145185188279053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-408720678890315465065777844222095700000000000000)
      constant := (11016088024300306836213067000241491383818190187065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree118.table
  base := (103170820733607944897029509508974191068779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-301449624635480436448675681103300000000000000)
      constant := (8199488615166554989722246588511323988070932811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134852798553379578423/25000000000000000000)
  centralHi := (539411194213518313693/100000000000000000000)
  directionLo := (541711465605082583769/100000000000000000000)
  directionHi := (54171146560508258377/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree119.table
  base := (21163304490206700257509877525828073471157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-412332939749702554429369160750357500000000000000)
      constant := (11214479826552017245711727136018908196868343889985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree119.table
  base := (105816499651542055517584581614477451904911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-304112775015216565736020362446500000000000000)
      constant := (8347060290027285632083726284899780691257948399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541711465605082583769/100000000000000000000)
  centralHi := (54171146560508258377/10000000000000000000)
  directionLo := (272001005279925008417/50000000000000000000)
  directionHi := (108800402111970003367/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree120.table
  base := (1695187157045762654329784494685918223839/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-415945200609089643792960477278619300000000000000)
      constant := (11414636950040197742442666874968286717119630113216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree120.table
  base := (10849195721162972305899571460903069279891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-153387962697476347511682521894850000000000000)
      constant := (4247972163468673068972769179997674400196396095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272001005279925008417/50000000000000000000)
  centralHi := (108800402111970003367/20000000000000000000)
  directionLo := (273141475712821654627/50000000000000000000)
  directionHi := (109256590285128661851/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree121.table
  base := (11119721227049070456245737560176775981487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-419557461468476733156551793806881100000000000000)
      constant := (11616559394142727890406596420523541219579104479270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree121.table
  base := (111197193223733619087368628440665416243807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-309439075774688824310709725132900000000000000)
      constant := (8646140725476723148797210349163229904482569663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273141475712821654627/50000000000000000000)
  centralHi := (109256590285128661851/20000000000000000000)
  directionLo := (274277204003296802123/50000000000000000000)
  directionHi := (548554408006593604247/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree122.table
  base := (22786444984414004478819586771131947779969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-423169722327863822520143110335142900000000000000)
      constant := (11820247158292133915295495890805161285261538161245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree122.table
  base := (28483051878616981682705315021239504310967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-156051113077212476799027203238050000000000000)
      constant := (4398824742631203697584377387591236130045852206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274277204003296802123/50000000000000000000)
  centralHi := (548554408006593604247/100000000000000000000)
  directionLo := (550816497636569490767/100000000000000000000)
  directionHi := (34426031102285593173/6250000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree123.table
  base := (11669701583440745297115604984926161322407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-426781983187250911883734426863404700000000000000)
      constant := (12025700241970506940080570358622730879044787792470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree123.table
  base := (11669699992562913702610995515468417024463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-157382688267080541442699543909650000000000000)
      constant := (4475235302972463662880183202755848666035193835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550816497636569490767/100000000000000000000)
  centralHi := (34426031102285593173/6250000000000000000)
  directionLo := (553069335249902967777/100000000000000000000)
  directionHi := (276534667624951483889/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree124.table
  base := (7468224053194499195681357191580442060293/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-430394244046638001247325743391666500000000000000)
      constant := (12232918644704901629741615587888945608381045239248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree124.table
  base := (59745785156388168626919976853817358437909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-158714263456948606086371884581250000000000000)
      constant := (4552302043602606482187451107719282544789340981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553069335249902967777/100000000000000000000)
  centralHi := (276534667624951483889/50000000000000000000)
  directionLo := (555313033449533002701/100000000000000000000)
  directionHi := (277656516724766501351/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree125.table
  base := (122315931829283019866433189077277677968801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-434006504906025090610917059919928300000000000000)
      constant := (12441902366063169263764554880443603548776688448921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree125.table
  base := (30578979635986644507484873446157603592211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-160045838646816670730044225252850000000000000)
      constant := (4630024964375879077911473841397624292670388198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555313033449533002701/100000000000000000000)
  centralHi := (277656516724766501351/50000000000000000000)
  directionLo := (557547702572681001977/100000000000000000000)
  directionHi := (278773851286340500989/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree126.table
  base := (3911564269945699367920592203948363960177/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-437618765765412179974508376448190100000000000000)
      constant := (12652651405650183722184070756423349671763661741344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree126.table
  base := (62585022249246157739546380642934115424089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-161377413836684735373716565924450000000000000)
      constant := (4708404065159026237841965087117641460971812601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557547702572681001977/100000000000000000000)
  centralHi := (278773851286340500989/50000000000000000000)
  directionLo := (111954690150833315707/20000000000000000000)
  directionHi := (69971681344270822317/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree127.table
  base := (4001686223703246504329483530999306249423/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-441231026624799269338099692976451900000000000000)
      constant := (12865165763104422895483109858233837096457962629856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree127.table
  base := (32013487016507298477430988878352001154313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-162708989026552800017388906596050000000000000)
      constant := (4787439345830128441117579373008459141099754834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111954690150833315707/20000000000000000000)
  centralHi := (69971681344270822317/12500000000000000000)
  directionLo := (561990383987466420521/100000000000000000000)
  directionHi := (280995191993733210261/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree128.table
  base := (26193527856109850021755141870638122824047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-444843287484186358701691009504713700000000000000)
      constant := (13079445438094871655572791977144528153163899188435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree128.table
  base := (32741907286370894346438828389655488159483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (59925)
      previous := (52734)
      next := (0)
      square := (1422364407359069051195454808300000000000000)
      linear := (-164040564216420864661061247267650000000000000)
      constant := (4867130806277549856846918809937497946688595894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell029.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561990383987466420521/100000000000000000000)
  centralHi := (280995191993733210261/50000000000000000000)
  directionLo := (70524825772951726743/12500000000000000000)
  directionHi := (112839721236722762789/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree129.table
  base := (133911096904100161543107157628254430171789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (165404985)
      previous := (143055357)
      next := (0)
      square := (3894433747349131062173155265125400000000000000)
      linear := (-448455548343573448065282326032975500000000000000)
      constant := (13295490430318215794635785376293926515625540722469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree129.table
  base := (26782217528846053656505667344809905871609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (119850)
      previous := (105468)
      next := (0)
      square := (2844728814718138102390909616600000000000000)
      linear := (-330744278812577858609467175878500000000000000)
      constant := (9894956892797971908507096172186825410351921405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell029.Kernel129
