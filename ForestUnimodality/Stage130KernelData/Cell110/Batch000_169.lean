import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell110.Parameters
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch000_049
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch050_099
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch100_149
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch150_199
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q22647_43472.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree000.table
  base := (8894124574419180255912209479/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (619052621189006765933804390000000000000)
      linear := (-31410063100363186730512588000000000000)
      constant := (889412457441918025591220947900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree000.table
  base := (8894124574419180255912209479/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (619052621189006765933804390000000000000)
      linear := (-31410063100363186730512588000000000000)
      constant := (889412457441918025591220947900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree001.table
  base := (483950947969079762701678541414482645939603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-453459196179692463196881162158369500000000000)
      constant := (324902467614330970115488544151057099488671633697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree001.table
  base := (96700780883077716185223250484837422176511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-453937027421672727794336317421900750000000000)
      constant := (324602718046478271079091005624463696246484277945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1561127038428610943/3125000000000000000)
  directionHi := (49956065229715550177/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree002.table
  base := (279771099885169058984466964969232047198747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-885839130422794292142102057022527000000000000)
      constant := (188226048402689895255720432347476399768031912953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree002.table
  base := (279322095388215596833644616846551371217329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-886794792906754821337012367549589500000000000)
      constant := (187925741345090065614933099940309418453828274571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1561127038428610943/3125000000000000000)
  centralHi := (49956065229715550177/100000000000000000000)
  directionLo := (70648544970658737057/100000000000000000000)
  directionHi := (35324272485329368529/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree003.table
  base := (174294336120967075290673399347152252320643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-1318219064665896121087322951886684500000000000)
      constant := (118014172649314826742942207440226124911381196657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree003.table
  base := (6957919697236060568615701164609126718843/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-119968414399257901352698947061570750000000000)
      constant := (10707637930654658750034805485253179698184814675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70648544970658737057/100000000000000000000)
  centralHi := (35324272485329368529/50000000000000000000)
  directionLo := (86526443124092330247/100000000000000000000)
  directionHi := (10815805390511541281/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree004.table
  base := (1470240393171866284856044413494879953419/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-1750598998908997950032543846750842000000000000)
      constant := (80778043788660569424632130238984805848762998480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree004.table
  base := (29343238560666482566580940446623485181663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-1752510323876919008422364467804967000000000000)
      constant := (80616796554499385443383279615634933252715430548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86526443124092330247/100000000000000000000)
  centralHi := (10815805390511541281/12500000000000000000)
  directionLo := (99912130459431100353/100000000000000000000)
  directionHi := (49956065229715550177/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree005.table
  base := (42705220280751412337590721618896672526091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-2182978933152099778977764741614999500000000000)
      constant := (60186235910469576847404307316249143102424288018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree005.table
  base := (10654689139717696916550355891658375389351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-2185368089362001101965040517932655750000000000)
      constant := (60076464879111774296380809417682495531157033992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99912130459431100353/100000000000000000000)
  centralHi := (49956065229715550177/50000000000000000000)
  directionLo := (27926289435514404311/25000000000000000000)
  directionHi := (22341031548411523449/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree006.table
  base := (65742911942752348034099281241814672252603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-2615358867395201607922985636479157000000000000)
      constant := (48235858877153281410175902423805669859049620697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree006.table
  base := (8202287006028841482134671038549198201921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-2618225854847083195507716568060344500000000000)
      constant := (48161258508811262454890679350219615944137849432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27926289435514404311/25000000000000000000)
  centralHi := (22341031548411523449/20000000000000000000)
  directionLo := (15295858671249451237/12500000000000000000)
  directionHi := (122366869369995609897/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree007.table
  base := (41197026952124953619170698238041793279/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3047738801638303436868206531343314500000000000)
      constant := (40977863440772911569515135687082284848761834880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree007.table
  base := (26319026744010499347451157404108273484833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3051083620332165289050392618188033250000000000)
      constant := (40926961150451363622605888309252490650108382934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15295858671249451237/12500000000000000000)
  centralHi := (122366869369995609897/100000000000000000000)
  directionLo := (132171325077148124789/100000000000000000000)
  directionHi := (13217132507714812479/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree008.table
  base := (5429657730990933236917304844201964526039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3480118735881405265813427426207472000000000000)
      constant := (36438529737744871347968275425343439531681974888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree008.table
  base := (5420284685380546378599057097609034223677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3483941385817247382593068668315722000000000000)
      constant := (36404227450564993834785355626425300567803288184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132171325077148124789/100000000000000000000)
  centralHi := (13217132507714812479/10000000000000000000)
  directionLo := (70648544970658737057/50000000000000000000)
  directionHi := (28259417988263494823/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree009.table
  base := (4544712535087744730441849450277362787951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3912498670124507094758648321071629500000000000)
      constant := (33610931627921342950018345003713971898299025192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree009.table
  base := (9073782798713894470691055376350435874611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-3916799151302329476135744718443410750000000000)
      constant := (33589202802708370184717481632275166605374769956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70648544970658737057/50000000000000000000)
  centralHi := (28259417988263494823/20000000000000000000)
  directionLo := (14986819568914665053/10000000000000000000)
  directionHi := (149868195689146650531/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree010.table
  base := (15351566711765195296096171134350488987837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-394988964033418993063988110539617000000000000)
      constant := (2905877119764918928846472896234957340317895066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree010.table
  base := (7662276823079790218190686405515586948333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-4349656916787411569678420768571099500000000000)
      constant := (31953391824463817686321431580942184073007311868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14986819568914665053/10000000000000000000)
  centralHi := (149868195689146650531/100000000000000000000)
  directionLo := (157974949065843821371/100000000000000000000)
  directionHi := (39493737266460955343/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree011.table
  base := (13018615241774358758174855280165279038773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-434296230782791886604462737345449500000000000)
      constant := (2836987149769354393080172432471025111503003914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree011.table
  base := (12994777573024052866549470816211812920427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-434774062024772151201917892608980750000000000)
      constant := (2836827355736394586627956776483379012362161686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157974949065843821371/100000000000000000000)
  centralHi := (39493737266460955343/25000000000000000000)
  directionLo := (165685524369486016409/100000000000000000000)
  directionHi := (16568552436948601641/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree012.table
  base := (22103594112160576334390316955245511096397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-5209638472853812581594311005664102000000000000)
      constant := (31165494613822043138899822114566053751280930303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree012.table
  base := (110305071780042891528481390176670307321/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-5215372447757575756763772868826477000000000000)
      constant := (31172890849615632414824758299508840439563155800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165685524369486016409/100000000000000000000)
  centralHi := (16568552436948601641/10000000000000000000)
  directionLo := (86526443124092330247/50000000000000000000)
  directionHi := (34610577249636932099/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree013.table
  base := (18740059451546051867550165015136413905731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-33384724302348605979523857399575500000000000)
      constant := (187761701435345889975216796952578980869657801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree013.table
  base := (18701821976970005946961065203213684333593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-33421480551731703256251177035231750000000000)
      constant := (187859584574724269239822788994898860801197803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86526443124092330247/50000000000000000000)
  centralHi := (34610577249636932099/20000000000000000000)
  directionLo := (9005957735308157461/5000000000000000000)
  directionHi := (180119154706163149221/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree014.table
  base := (197950687445827966710300173615915909963/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-6074398341340016239484752795392417000000000000)
      constant := (32831353006585930824133708338756610225820746960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree014.table
  base := (15801665925345659981237204097716727330653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-552826179884339994895374997189259500000000000)
      constant := (2987018855877788880501751932242687661465808877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9005957735308157461/5000000000000000000)
  centralHi := (180119154706163149221/100000000000000000000)
  directionLo := (9345924024046302067/5000000000000000000)
  directionHi := (186918480480926041341/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree015.table
  base := (13311009385019745640510564865929851429003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-6506778275583118068429973690256574500000000000)
      constant := (34410299647069448011301391211737575645402484297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree015.table
  base := (13280104854831275305628422836132170891267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-6513945744212822037391801019209543250000000000)
      constant := (34445719607134014960503832878888328323270892433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9345924024046302067/5000000000000000000)
  centralHi := (186918480480926041341/100000000000000000000)
  directionLo := (193479008676739721597/100000000000000000000)
  directionHi := (96739504338369860799/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree016.table
  base := (277577619123066639811753452317133857247/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-6939158209826219897375194585120732000000000000)
      constant := (36427081563563488854207534294649000578584178120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree016.table
  base := (11075384986444513672914620771982341503821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-6946803509697904130934477069337232000000000000)
      constant := (36472363471242145111112573889043679400872769279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193479008676739721597/100000000000000000000)
  centralHi := (96739504338369860799/50000000000000000000)
  directionLo := (199824260918862200707/100000000000000000000)
  directionHi := (49956065229715550177/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree017.table
  base := (1832633491049933805985629441780124183821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-7371538144069321726320415479984889500000000000)
      constant := (38848698348509625748142275455452305079440446395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree017.table
  base := (4569182515689516030326199616390816464047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-7379661275182986224477153119464920750000000000)
      constant := (38904160337203420141326751879429199646723455306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199824260918862200707/100000000000000000000)
  centralHi := (49956065229715550177/25000000000000000000)
  directionLo := (257467666977953741/125000000000000000)
  directionHi := (205974133582362992801/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree018.table
  base := (7451151651354784698262296283287309128881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-7803918078312423555265636374849047000000000000)
      constant := (41648275302455752030099846516955813994082910219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree018.table
  base := (1857254409062271037219399795568061294693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-7812519040668068318019829169592609500000000000)
      constant := (41714247888188019081564739684971315748478710428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257467666977953741/125000000000000000)
  centralHi := (205974133582362992801/100000000000000000000)
  directionLo := (211945634911976211171/100000000000000000000)
  directionHi := (52986408727994052793/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree019.table
  base := (1483491685757537152005725870297431248907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-22815229951677355634933122630784500000000000)
      constant := (124109710110753408267658048336852980016872452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree019.table
  base := (5914265434552016623667465625474486531669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-22840378964413159034799183434128250000000000)
      constant := (124322515059870852619130998203030890774872671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211945634911976211171/100000000000000000000)
  centralHi := (52986408727994052793/25000000000000000000)
  directionLo := (217753439953256087099/100000000000000000000)
  directionHi := (2177534399532560871/1000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree020.table
  base := (143250907935614531058133300826353263439/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-8668677946798627213156078164577362000000000000)
      constant := (48296177113482833279685981801575777659700782752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree020.table
  base := (4566536761688137703245619689680245467821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-8678234571638232505105181269847987000000000000)
      constant := (48384197165938307728093057793302166178209205279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217753439953256087099/100000000000000000000)
  centralHi := (2177534399532560871/1000000000000000000)
  directionLo := (27926289435514404311/12500000000000000000)
  directionHi := (223410315484115234489/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree021.table
  base := (675645284956462099791145516741897412991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-827368898276520822009209005403774500000000000)
      constant := (4737316367814868476504225720927345190095839595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree021.table
  base := (3362731798900252961342269638403644522961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-9111092337123314598647857319975675750000000000)
      constant := (52210053310894674457049811046431423693527104139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27926289435514404311/12500000000000000000)
  centralHi := (223410315484115234489/100000000000000000000)
  directionLo := (57231862584330753123/25000000000000000000)
  directionHi := (228927450337323012493/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree022.table
  base := (91885398801753693525935063458578455797/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-866676165025893715549683632209607000000000000)
      constant := (5112134436116310677393395948979783700242979325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree022.table
  base := (2283439729779117323020359883332507430043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-867631827509854244744593942736669500000000000)
      constant := (5122269981091004547439215185674655539549493387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57231862584330753123/25000000000000000000)
  centralHi := (228927450337323012493/100000000000000000000)
  directionLo := (14644669728264067011/6250000000000000000)
  directionHi := (234314715652225072177/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree023.table
  base := (1324401996214825916373443369720999810849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-9965817749527932699991740849169834500000000000)
      constant := (60654199091168937861715227738342585033310953051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree023.table
  base := (52492861951300029239077079236617186467/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-9976807868093478785733209420231053250000000000)
      constant := (60777981518977049373211764317267623875832930825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14644669728264067011/6250000000000000000)
  centralHi := (234314715652225072177/100000000000000000000)
  directionLo := (239580872409336309679/100000000000000000000)
  directionHi := (2994760905116703871/1250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree024.table
  base := (446246529634093907754666971160691280201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-10398197683771034528936961744033992000000000000)
      constant := (65363392529989078741481866973344766757451610899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree024.table
  base := (435610296138622234636082900117821626329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-10409665633578560879275885470358742000000000000)
      constant := (65499849498886790087040474989231380475607765571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239580872409336309679/100000000000000000000)
  centralHi := (2994760905116703871/1250000000000000000)
  directionLo := (15295858671249451237/6250000000000000000)
  directionHi := (244733738739991219793/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree025.table
  base := (-348951867979892807009553859768583173753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-10830577618014136357882182638898149500000000000)
      constant := (70353260649229537469203087846139889381927535453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree025.table
  base := (-179150224149835790671422994940412328741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-985683945369422088438051047316948250000000000)
      constant := (6409344061343267059403253484122042604409180662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15295858671249451237/6250000000000000000)
  centralHi := (244733738739991219793/100000000000000000000)
  directionLo := (62445081537144437721/25000000000000000000)
  directionHi := (49956065229715550177/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree026.table
  base := (-1070995092981383671362973150534716245259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-66644719244125669744540849312203000000000000)
      constant := (447439203586088009453451067885492766790076511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree026.table
  base := (-2158397685302015838524925887877788967/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-66718231742891864297995488583515500000000000)
      constant := (448403658127332777961891299312832431256021500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62445081537144437721/25000000000000000000)
  centralHi := (49956065229715550177/20000000000000000000)
  directionLo := (254726951428633615427/100000000000000000000)
  directionHi := (63681737857158403857/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree027.table
  base := (-86407633991005721863077512188250600663/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-11695337486500340015772624428626464500000000000)
      constant := (81149737124147403913370402493992090234163227260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree027.table
  base := (-21691764839085279086533908213843132261/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-11708238930033807159903913620741808250000000000)
      constant := (81326609350301101368719003679905944030434512880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254726951428633615427/100000000000000000000)
  centralHi := (63681737857158403857/25000000000000000000)
  directionLo := (129789664686138495371/50000000000000000000)
  directionHi := (259579329372276990743/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree028.table
  base := (-232740212958492505721244741530393454961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-12127717420743441844717845323490622000000000000)
      constant := (86946113209521909013126999814014383327691278610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree028.table
  base := (-583423103663578238844796826206610512659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-12141096695518889253446589670869497000000000000)
      constant := (87137283895599013580938653760108683691260231036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129789664686138495371/50000000000000000000)
  centralHi := (259579329372276990743/100000000000000000000)
  directionLo := (264342650154296249579/100000000000000000000)
  directionHi := (13217132507714812479/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree029.table
  base := (-2874631150435466251320916653421247848941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-12560097354986543673663066218354779500000000000)
      constant := (93002402427114155458291107928639306521073543841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree029.table
  base := (-2880128438098253612933214949728076292537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-12573954461003971346989265720997185750000000000)
      constant := (93208298540165339274241366862972488110967211837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264342650154296249579/100000000000000000000)
  centralHi := (13217132507714812479/5000000000000000000)
  directionLo := (269021644377979843591/100000000000000000000)
  directionHi := (33627705547247480449/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree030.table
  base := (-3374808049431709206452042631322026342313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-12992477289229645502608287113218937000000000000)
      constant := (99315270551024503645328755378763607568700088013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree030.table
  base := (-844901650798472880653882855710594697911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-13006812226489053440531941771124874500000000000)
      constant := (99536326414234499772498439203028938216556503244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269021644377979843591/100000000000000000000)
  centralHi := (33627705547247480449/12500000000000000000)
  directionLo := (68405159526286762103/25000000000000000000)
  directionHi := (273620638105147048413/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree031.table
  base := (-958031347501706434935841637637535339633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-13424857223472747331553508008083094500000000000)
      constant := (105881903956125515400930755401572395965680533332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree031.table
  base := (-959077342797026844642097739837520639943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-13439669991974135534074617821252563250000000000)
      constant := (106118560672246174688751698105302479264532070572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68405159526286762103/25000000000000000000)
  centralHi := (273620638105147048413/100000000000000000000)
  directionLo := (55628719938644442591/20000000000000000000)
  directionHi := (69535899923305553239/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree032.table
  base := (-425012115763470521965322883385320377867/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1259748832519622650954429900267932000000000000)
      constant := (10245448027627604458528553108881833890667121970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree032.table
  base := (-425376548249152468050273852434482487807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-13872527757459217627617293871380252000000000000)
      constant := (112952633180039535002968628114663736369152101070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55628719938644442591/20000000000000000000)
  centralHi := (69535899923305553239/25000000000000000000)
  directionLo := (70648544970658737057/25000000000000000000)
  directionHi := (282594179882634948229/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree033.table
  base := (-2315890489197814645166687401853474098843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1299056099268995544494904527073764500000000000)
      constant := (10887939994880186694806377239361708641157374826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree033.table
  base := (-2317476076709727814229157417189742635603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1300489592994936338287269992864358250000000000)
      constant := (10912413266429326455728614479634071694026493146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70648544970658737057/25000000000000000000)
  centralHi := (282594179882634948229/100000000000000000000)
  directionLo := (143487873143320576789/50000000000000000000)
  directionHi := (286975746286641153579/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree034.table
  base := (-995924872909066983246777099041733046131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-14721997026202052818389170692675567000000000000)
      constant := (127082448033305416376993466774835506097372660155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree034.table
  base := (-4982381286107344441677298546166543636421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-14738243288429381814702645971635629500000000000)
      constant := (127368613189284148238800884734894547513391503321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143487873143320576789/50000000000000000000)
  centralHi := (286975746286641153579/100000000000000000000)
  directionLo := (145645706605112658923/50000000000000000000)
  directionHi := (291291413210225317847/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree035.table
  base := (-2647888744273171481280625507460381731467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-15154376960445154647334391587539724500000000000)
      constant := (134643825700560311956064825319246380092038455534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree035.table
  base := (-662271524722659022074552309561521414803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-15171101053914463908245322021763318250000000000)
      constant := (134947412684053100909433372219206630203189472024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145645706605112658923/50000000000000000000)
  centralHi := (291291413210225317847/100000000000000000000)
  directionLo := (147772033774362921381/50000000000000000000)
  directionHi := (295544067548725842763/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree036.table
  base := (-1116406918492416636276982585887797926579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-15586756894688256476279612482403882000000000000)
      constant := (142450268831392214736900175100310577996353798395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree036.table
  base := (-1116822595986504110439291784779467700011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1418541710854504181980727097444637000000000000)
      constant := (12979249493510703759507812396994953650450144505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147772033774362921381/50000000000000000000)
  centralHi := (295544067548725842763/100000000000000000000)
  directionLo := (14986819568914665053/5000000000000000000)
  directionHi := (299736391378293301061/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree037.table
  base := (-5839909808736980246522807375645862003337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-16019136828931358305224833377268039500000000000)
      constant := (150500761293031803765324972994502378686672542637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree037.table
  base := (-584171226618304978919398368722950819977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-16036816584884628095330674122018695750000000000)
      constant := (150840595980463005692095911929265393784455052770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14986819568914665053/5000000000000000000)
  centralHi := (299736391378293301061/100000000000000000000)
  directionLo := (30387088174044747341/10000000000000000000)
  directionHi := (303870881740447473411/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree038.table
  base := (-6070680890173416487648191030694038010979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-45572068596051136105734222360477000000000000)
      constant := (439873810489892390754232205315903908337590039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree038.table
  base := (-759030363587870686694763425437251835557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-45622366621522742905466343967164500000000000)
      constant := (440867349389945673739343579064783971951596296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30387088174044747341/10000000000000000000)
  centralHi := (303870881740447473411/100000000000000000000)
  directionLo := (307949868035290134741/100000000000000000000)
  directionHi := (153974934017645067371/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree039.table
  base := (-6275426112626821838758018238006915413013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-99904714185902733509557841224830500000000000)
      constant := (990121882147940588488066937343256070144925377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree039.table
  base := (-627677882818511380806833676831281191163/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-100014982934052025339739800131799250000000000)
      constant := (992358432955247577422687056463859206711417270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307949868035290134741/100000000000000000000)
  centralHi := (153974934017645067371/50000000000000000000)
  directionLo := (155987763683716713861/50000000000000000000)
  directionHi := (311975527367433427723/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree040.table
  base := (-3227527708231856008966515615073450358043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-17316276631660663792060496061860512000000000000)
      constant := (176108608121414194610053163838878875076335401486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree040.table
  base := (-1614056526115488264654712153090226901733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-17335389881339874375958702272401762000000000000)
      constant := (176506374030192879835639897252383749765895541732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155987763683716713861/50000000000000000000)
  centralHi := (311975527367433427723/100000000000000000000)
  directionLo := (157974949065843821371/50000000000000000000)
  directionHi := (315949898131687642743/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree041.table
  base := (-3305168343147450788327727399048166064979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-17748656565903765621005716956724669500000000000)
      constant := (185127960375493425494302210827643652385167316158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree041.table
  base := (-206604662749185733463478797482824608251/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-17768247646824956469501378322529450750000000000)
      constant := (185545996676690383556565903296446622868588088832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157974949065843821371/50000000000000000000)
  centralHi := (315949898131687642743/100000000000000000000)
  directionLo := (319874892079168029169/100000000000000000000)
  directionHi := (31987489207916802917/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree042.table
  base := (-3370958964008652499015217192381806808249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-18181036500146867449950937851588827000000000000)
      constant := (194388219969130238694533073375714220790581808698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree042.table
  base := (-6742793131557369566880329526194021401589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-18201105412310038563044054372657139500000000000)
      constant := (194827010254881914040665296213184031962665023689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319874892079168029169/100000000000000000000)
  centralHi := (31987489207916802917/10000000000000000000)
  directionLo := (323752305066535377297/100000000000000000000)
  directionHi := (161876152533267688649/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree043.table
  base := (-6850345983676617898195244981961077336919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1692128766762724479899650795132089500000000000)
      constant := (18535365447015873629859240215760028726501908729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree043.table
  base := (-1370220412660067671485297137386716163941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-18633963177795120656586730422784828250000000000)
      constant := (204349049560685730761190749242440268603289294205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323752305066535377297/100000000000000000000)
  centralHi := (161876152533267688649/50000000000000000000)
  directionLo := (327583826659880422579/100000000000000000000)
  directionHi := (16379191332994021129/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree044.table
  base := (-216752572645560011951477432787080672209/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1731436033512097373440125421937922000000000000)
      constant := (19420913684240134847497540349429471348614435808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree044.table
  base := (-433545946316462105885301357548022224487/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1733347358480018431829946042992047000000000000)
      constant := (19464709678831160054528507117505410768700361872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327583826659880422579/100000000000000000000)
  centralHi := (16379191332994021129/5000000000000000000)
  directionLo := (331371048738972032819/100000000000000000000)
  directionHi := (16568552436948601641/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree045.table
  base := (-6999516379324538031759076853831129626109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-19478176302876172936786600536181299500000000000)
      constant := (223611050452545659442531884569943592270297876209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree045.table
  base := (-7000079744767461131241346198701024006463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-19499678708765284843672082523040205750000000000)
      constant := (224115021003975450338071951157550455123099187163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331371048738972032819/100000000000000000000)
  centralHi := (16568552436948601641/5000000000000000000)
  directionLo := (83778868306543212933/25000000000000000000)
  directionHi := (335115473226172851733/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree046.table
  base := (-7040976780015795881574228240360516797729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-19910556237119274765731821431045457000000000000)
      constant := (233831799150052849596667309266943787662560865829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree046.table
  base := (-3520731355633150497872433471839647368363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-19932536474250366937214758573167894500000000000)
      constant := (234358473831298078274216895996240694262727918126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83778868306543212933/25000000000000000000)
  centralHi := (335115473226172851733/100000000000000000000)
  directionLo := (338818519046461461851/100000000000000000000)
  directionHi := (84704629761615365463/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree047.table
  base := (-1412148170844582520487416884613063422211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-20342936171362376594677042325909614500000000000)
      constant := (244292110504961024426295573573846781033338100555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree047.table
  base := (-7061159796477509447067451454312079075321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-1851399476339586275523403147572325750000000000)
      constant := (22258361808144554685752414154761935828631241111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338818519046461461851/100000000000000000000)
  centralHi := (84704629761615365463/25000000000000000000)
  directionLo := (171240764205017027363/50000000000000000000)
  directionHi := (342481528410034054727/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree048.table
  base := (-1764760658513179506166529230094181851779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-20775316105605478423622263220773772000000000000)
      constant := (254991827458557322539119781573104914613811859516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree048.table
  base := (-27575795541809465047446076239149289693/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-20798252005220531124300110673423272000000000000)
      constant := (255565383042097614597316012230665452614097252608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171240764205017027363/50000000000000000000)
  centralHi := (342481528410034054727/100000000000000000000)
  directionLo := (346105772496369320989/100000000000000000000)
  directionHi := (34610577249636932099/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree049.table
  base := (-3518039807648067038409756429129312689143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-21207696039848580252567484115637929500000000000)
      constant := (265930817471613952019806462442670956048507643686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree049.table
  base := (-1759097648564890645889966146048174006913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-21231109770705613217842786723550960750000000000)
      constant := (266528551554559165101978428665167060958851270452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346105772496369320989/100000000000000000000)
  centralHi := (34610577249636932099/10000000000000000000)
  directionLo := (349692456608008851237/100000000000000000000)
  directionHi := (174846228304004425619/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree050.table
  base := (-69920184613063324228239401990350308187/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-21640075974091682081512705010502087000000000000)
      constant := (277108968696521262717866093239697217977601248700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree050.table
  base := (-3414202256060963385069213590359353321/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-21663967536190695311385462773678649500000000000)
      constant := (277731374281392939635340426878173544533100692608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349692456608008851237/100000000000000000000)
  centralHi := (174846228304004425619/50000000000000000000)
  directionLo := (70648544970658737057/20000000000000000000)
  directionHi := (176621362426646842643/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree051.table
  base := (-6926999816417132350025821189941679506567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-22072455908334783910457925905366244500000000000)
      constant := (288526186747007472843379777340486045356072392867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree051.table
  base := (-1385446054028992850588737310824528033563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-22096825301675777404928138823806338250000000000)
      constant := (289173757447934538280247017012873920938832021315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70648544970658737057/20000000000000000000)
  centralHi := (176621362426646842643/50000000000000000000)
  directionLo := (44594708051203953787/12500000000000000000)
  directionHi := (356757664409631630297/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree052.table
  base := (-3420571183957684030798243267312211106773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-133164709127679797274574833137458000000000000)
      constant := (1776227171432858433428600224148824919390008834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree052.table
  base := (-684134063755740599196570827044072538427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-133311734125212186381484111680083000000000000)
      constant := (1780210780683848118266076217853864004499063830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44594708051203953787/12500000000000000000)
  centralHi := (356757664409631630297/100000000000000000000)
  directionLo := (9005957735308157461/2500000000000000000)
  directionHi := (360238309412326298441/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree053.table
  base := (-1683636568469725182660722233933961050453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-22937215776820987568348367695094559500000000000)
      constant := (312077517155972175380616172009895868723258168612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree053.table
  base := (-1683679197757417739569754501289095502909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-22962540832645941592013490924061715750000000000)
      constant := (312776900991170311564835190265390859946185592036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9005957735308157461/2500000000000000000)
  centralHi := (360238309412326298441/100000000000000000000)
  directionLo := (90921411127098705637/25000000000000000000)
  directionHi := (363685644508394822549/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree054.table
  base := (-6607296055877904326293727538395509517187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2124508701005826308844871689996247000000000000)
      constant := (29473773234193050096038152623557165734865938317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree054.table
  base := (-6607442652943696220871996845398441311263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-23395398598131023685556166974189404500000000000)
      constant := (324937538294507881428790911797946378965702711963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90921411127098705637/25000000000000000000)
  centralHi := (363685644508394822549/100000000000000000000)
  directionLo := (45887576013748353711/12500000000000000000)
  directionHi := (367100608109986829689/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree055.table
  base := (-6459463040082095159459748571065330065217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2163815967755199202385346316802079500000000000)
      constant := (30598573578698730166391642504152337621801176047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree055.table
  base := (-6459589029343305339688530741713430239283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2166205123965100525372622093119735750000000000)
      constant := (30667044211610712511961751227040340920469083453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45887576013748353711/12500000000000000000)
  centralHi := (367100608109986829689/100000000000000000000)
  directionLo := (370484095377868715167/100000000000000000000)
  directionHi := (11577627980558397349/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree056.table
  base := (-3145553708637178672957353410422629720733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-24234355579550293055184030379687032000000000000)
      constant := (349195888130685414955069687005668549234091608866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree056.table
  base := (-1258243131973605403765235237980154906253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-24261114129101187872641519074444782000000000000)
      constant := (349976704999587832099409079297108474612842589765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370484095377868715167/100000000000000000000)
  centralHi := (11577627980558397349/3125000000000000000)
  directionLo := (9345924024046302067/2500000000000000000)
  directionHi := (373836960961852082681/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree057.table
  base := (-3051139990632537974130909593648325092871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-68328907240424916576535322090169500000000000)
      constant := (1002898082502621453810461443160744058554705622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree057.table
  base := (-6102372947307553381699479709136888641957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-68404354278632326776133504500200750000000000)
      constant := (1005138948711512756891825430588553406827101937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9345924024046302067/2500000000000000000)
  centralHi := (373836960961852082681/100000000000000000000)
  directionLo := (75432004304387647103/20000000000000000000)
  directionHi := (94290005380484558879/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree058.table
  base := (-736627949489195686749833291819629047549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-25099115448036496713074472169415347000000000000)
      constant := (375135239558075699321739650585633849251551309192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree058.table
  base := (-1178620683369610136389294588131363832743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2284257241824668369066079197700014500000000000)
      constant := (34179347658628431460049885230647315213390911565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75432004304387647103/20000000000000000000)
  centralHi := (94290005380484558879/25000000000000000000)
  directionLo := (380454058051250792507/100000000000000000000)
  directionHi := (95113514512812698127/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree059.table
  base := (-5663374433125035731864625866987760556243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-25531495382279598542019693064279504500000000000)
      constant := (388462959179644064086389648248574980909715878943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree059.table
  base := (-5663442947256053583122224495050766795909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-25559687425556434153269547224827848250000000000)
      constant := (389329672201553411921031207591568063961844766009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380454058051250792507/100000000000000000000)
  centralHi := (95113514512812698127/25000000000000000000)
  directionLo := (95929954504869105737/25000000000000000000)
  directionHi := (383719818019476422949/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree060.table
  base := (-541336301757720659777007906916751902083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-25963875316522700370964913959143662000000000000)
      constant := (402029346163070745948257053000152529652640007830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree060.table
  base := (-2706710904821606331214350199699334145061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-25992545191041516246812223274955537000000000000)
      constant := (402925684039865345228686728407003251234167415922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95929954504869105737/25000000000000000000)
  centralHi := (383719818019476422949/100000000000000000000)
  directionLo := (77391603470695888639/20000000000000000000)
  directionHi := (96739504338369860799/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree061.table
  base := (-514301510834894652003164740550550908497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-26396255250765802199910134854007819500000000000)
      constant := (415834383221463675383967008492222944889835717970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree061.table
  base := (-5143065543884581628349992567351165512723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-26425402956526598340354899325083225750000000000)
      constant := (416760842620063937314805334384266997058389607423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77391603470695888639/20000000000000000000)
  centralHi := (96739504338369860799/25000000000000000000)
  directionLo := (97542335567489390541/25000000000000000000)
  directionHi := (78033868453991512433/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree062.table
  base := (-4852352442912960052491636172390894150919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-26828635185008904028855355748871977000000000000)
      constant := (429878055766826657840140497482684755451212410019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree062.table
  base := (-2426197849031578470362818285616294774289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-26858260722011680433897575375210914500000000000)
      constant := (430835133481252237338185173040308015167788852778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97542335567489390541/25000000000000000000)
  centralHi := (78033868453991512433/20000000000000000000)
  directionLo := (196677225486713946471/50000000000000000000)
  directionHi := (393354450973427892943/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree063.table
  base := (-2270696682489778003749432571289329094541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-27261015119252005857800576643736134500000000000)
      constant := (444160351488714048783119039370861864349215258882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree063.table
  base := (-9082860904695906657102018453227797759/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-27291118487496762527440251425338603250000000000)
      constant := (445148544422736999683212175989573450896178929500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196677225486713946471/50000000000000000000)
  centralHi := (393354450973427892943/100000000000000000000)
  directionLo := (396513975231444374369/100000000000000000000)
  directionHi := (39651397523144437437/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree064.table
  base := (-421015335432408659949612889595752411911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-27693395053495107686745797538600292000000000000)
      constant := (458681259998664089117142289156985529521189398110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree064.table
  base := (-842037029073442894245074150542088705471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-27723976252981844620982927475466292000000000000)
      constant := (459701065150780148644885179098208102059235586855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396513975231444374369/100000000000000000000)
  centralHi := (39651397523144437437/10000000000000000000)
  directionLo := (199824260918862200707/50000000000000000000)
  directionHi := (79929704367544880283/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree065.table
  base := (-385864547389988421352381608465096480421/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223477996249231442502103384790000000000000)
      linear := (-15129518551768805549053802277280500000000000)
      constant := (254674971775224239070436808529857095455680190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree065.table
  base := (-1929336359157780428575687969848401644421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-166608485316372347423228423228366750000000000)
      constant := (2807649035387922577562471296681542001952508418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199824260918862200707/50000000000000000000)
  centralHi := (79929704367544880283/20000000000000000000)
  directionLo := (402758673972781960157/100000000000000000000)
  directionHi := (201379336986390980079/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree066.table
  base := (-3486880747149681827054631011385562457449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2596195901998301031330567211666237000000000000)
      constant := (44403534698665997097188118062369344595033493959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree066.table
  base := (-3486904089652246190969005583683133109291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2599062889450182618915298143247424500000000000)
      constant := (44502127507700564897345399967291110075885265381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402758673972781960157/100000000000000000000)
  centralHi := (201379336986390980079/50000000000000000000)
  directionLo := (405844992470708288883/100000000000000000000)
  directionHi := (101461248117677072221/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree067.table
  base := (-3094868476412595260710091800410395351199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-28990534856224413173581460223192764500000000000)
      constant := (503675581221425933740420823852495447621455702299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree067.table
  base := (-3094888471238281129130789033941553218401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-29022549549437090901610955625849358250000000000)
      constant := (504793205781151331042575794607505768959496807301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405844992470708288883/100000000000000000000)
  centralHi := (101461248117677072221/25000000000000000000)
  directionLo := (40890801699989309779/10000000000000000000)
  directionHi := (408908016999893097791/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree068.table
  base := (-167663531976409384236116175683122876451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-29422914790467515002526681118056922000000000000)
      constant := (519150865870358949887422886976900529231785765616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree068.table
  base := (-2682633635064815772102057752951573839409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-29455407314922172995153631675977047000000000000)
      constant := (520302091354118778282114650561952735872946459509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40890801699989309779/10000000000000000000)
  centralHi := (408908016999893097791/100000000000000000000)
  directionLo := (411948267164725985601/100000000000000000000)
  directionHi := (205974133582362992801/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree069.table
  base := (-140633217316151414164091727935260068361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-29855294724710616831471902012921079500000000000)
      constant := (534864731186578087012493173282955893485378020176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree069.table
  base := (-2250146138294769061190928156694481693207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-2717115007309750462608755247827703250000000000)
      constant := (48731823173009370713711184716808589639816634137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411948267164725985601/100000000000000000000)
  centralHi := (205974133582362992801/50000000000000000000)
  directionLo := (25935390220915444237/6250000000000000000)
  directionHi := (414966243534647107793/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree070.table
  base := (-898709481347334591930278853619822714363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-30287674658953718660417122907785237000000000000)
      constant := (550817173418657077341925782577815474317427410126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree070.table
  base := (-1797431513132843589348083527262905655293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-30321122845892337182238983776232424500000000000)
      constant := (552037092715447186043274327976401938308888522993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25935390220915444237/6250000000000000000)
  centralHi := (414966243534647107793/100000000000000000000)
  directionLo := (417962428606318210959/100000000000000000000)
  directionHi := (5224530357578977637/1250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree071.table
  base := (-331120921419714847171161433053663632869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-30720054593196820489362343802649394500000000000)
      constant := (567008189400922904085399146178474490339830987876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree071.table
  base := (-1324494427020829813687901952817277365881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-30753980611377419275781659826360113250000000000)
      constant := (568263201658835584725489536815888715172347126781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417962428606318210959/100000000000000000000)
  centralHi := (5224530357578977637/1250000000000000000)
  directionLo := (13154290240754720601/3125000000000000000)
  directionHi := (420937287704151059233/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree072.table
  base := (-207832406649942308383355271472057279769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-31152434527439922318307564697513552000000000000)
      constant := (583437776462006420263165665388442549326417215476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree072.table
  base := (-83133881779600616065291398774692053369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-31186838376862501369324335876487802000000000000)
      constant := (584728379090589614182761502590834695876761174690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13154290240754720601/3125000000000000000)
  centralHi := (420937287704151059233/100000000000000000000)
  directionLo := (211945634911976211171/50000000000000000000)
  directionHi := (423891269823952422343/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree073.table
  base := (-317960144481625673828423982765652600199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-31584814461683024147252785592377709500000000000)
      constant := (600105932347669826189668899991305370086909051299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree073.table
  base := (-317968007725609989431894631141842075921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-31619696142347583462867011926615490750000000000)
      constant := (601432622781139053690575997588125575870003992821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211945634911976211171/50000000000000000000)
  centralHi := (423891269823952422343/100000000000000000000)
  directionLo := (42682480842401655373/10000000000000000000)
  directionHi := (426824808424016553731/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree074.table
  base := (107810963087156077101419536051781927167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-32017194395926125976198006487241867000000000000)
      constant := (617012655155682161359845706599030730724079693066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree074.table
  base := (43123040056239041587640539751684135549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-32052553907832665556409687976743179500000000000)
      constant := (618375930849454366538590514405734219889663991755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42682480842401655373/10000000000000000000)
  centralHi := (426824808424016553731/100000000000000000000)
  directionLo := (429738322167611702297/100000000000000000000)
  directionHi := (214869161083805851149/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree075.table
  base := (384707096749068478919612748668145018819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-32449574330169227805143227382106024500000000000)
      constant := (634157943280861922859458219146394993939218824162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree075.table
  base := (48088027593650196485835341782970127213/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-32485411673317747649952364026870868250000000000)
      constant := (635558301708570294633146599916490740768252773392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429738322167611702297/100000000000000000000)
  centralHi := (214869161083805851149/50000000000000000000)
  directionLo := (108158053905115412809/25000000000000000000)
  directionHi := (432632215620461651237/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree076.table
  base := (671707319572244156276067407556296511681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (30082)
      previous := (15041)
      next := (15041)
      square := (104619892980942143442812941910000000000000)
      linear := (-8280522353163517913394220165442000000000000)
      constant := (164074992538075939978082527922773528220948178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree076.table
  base := (671704860447588810757413336646040623859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-91186341935741910646800665033237000000000000)
      constant := (1808808127478181825023739230310780104039507762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108158053905115412809/25000000000000000000)
  centralHi := (432632215620461651237/100000000000000000000)
  directionLo := (435506879906512174199/100000000000000000000)
  directionHi := (2177534399532560871/500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree077.table
  base := (387524311994928238843263264577288501139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3028575836241402860275788106530394500000000000)
      constant := (60833110025110942774127524789328986564579946255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree077.table
  base := (1937617355351969289330134626364471505371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3031920654935264712457974193375113250000000000)
      constant := (60967293332097686608126808598941133690508679339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435506879906512174199/100000000000000000000)
  centralHi := (2177534399532560871/500000000000000000)
  directionLo := (438362693324991802169/100000000000000000000)
  directionHi := (43836269332499180217/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree078.table
  base := (1276016759421581960869716537957876667861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-199684699011233924804608816962713000000000000)
      constant := (4065237793129926031899526602479118581496152062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree078.table
  base := (5104059849815604496856868249042707081/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-199905236507532508464972734776650500000000000)
      constant := (4074199873704074823881177829106185326159325500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438362693324991802169/100000000000000000000)
  centralHi := (43836269332499180217/10000000000000000000)
  directionLo := (17648000877260921409/4000000000000000000)
  directionHi := (220600010965761517613/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree079.table
  base := (3186649303067770427918036656392764922461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-34179094067141635120924110961562654500000000000)
      constant := (705124724843081074782403220760647874427948654639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree079.table
  base := (3186646231627255992680920157263879499741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-34216842735258076024123068227381623250000000000)
      constant := (706678389224432653706899802820229399838709185359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17648000877260921409/4000000000000000000)
  centralHi := (220600010965761517613/50000000000000000000)
  directionLo := (11100480502145278819/2500000000000000000)
  directionHi := (444019220085811152761/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree080.table
  base := (48018348617286131407951248758597087493/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-34611474001384736949869331856426812000000000000)
      constant := (723462823001878595793824781794164619745557184560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree080.table
  base := (3841465264896264793690347997544326221991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3149972772794832556151431297955392000000000000)
      constant := (65914187061834953564188680104829791798477448919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11100480502145278819/2500000000000000000)
  centralHi := (444019220085811152761/100000000000000000000)
  directionLo := (446820630968230468977/100000000000000000000)
  directionHi := (223410315484115234489/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree081.table
  base := (4516488414364738742773684932927482731813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35043853935627838778814552751290969500000000000)
      constant := (742039480935907223444903321730960596015086972487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree081.table
  base := (2258243086070988387109744379259005619691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35082558266228240211208420327637000750000000000)
      constant := (743672783451083363411484061048907670395050520818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446820630968230468977/100000000000000000000)
  centralHi := (223410315484115234489/50000000000000000000)
  directionLo := (449604587067439951591/100000000000000000000)
  directionHi := (56200573383429993949/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree082.table
  base := (2605855074736843015820810481990445802291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35476233869870940607759773646155127000000000000)
      constant := (760854698156244741195190824743620764499943375618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree082.table
  base := (2605854117064473386228179828896375909451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35515416031713322304751096377764689500000000000)
      constant := (762528566054451088310478682674288670234163313298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449604587067439951591/100000000000000000000)
  centralHi := (56200573383429993949/12500000000000000000)
  directionLo := (452371410640989542999/100000000000000000000)
  directionHi := (452371410640989543/100000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree083.table
  base := (5927132479993091460896185355643340687517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35908613804114042436704994541019284500000000000)
      constant := (779908474250355426041027736913368620823301971183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree083.table
  base := (2963565422058213408608142422915926914213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-35948273797198404398293772427892378250000000000)
      constant := (781623405083104554680345281251322483405215360174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452371410640989542999/100000000000000000000)
  centralHi := (452371410640989543/100000000000000000)
  directionLo := (113780353537680875327/25000000000000000000)
  directionHi := (455121414150723501309/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree084.table
  base := (416422180453517932929390589860464227971/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-36340993738357144265650215435883442000000000000)
      constant := (799200808870162595684711151856796913426833762064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree084.table
  base := (3331376745136650617979840459870944205163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-36381131562683486491836448478020067000000000000)
      constant := (800957300193554412624358214897910732695281368274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113780353537680875327/25000000000000000000)
  centralHi := (455121414150723501309/100000000000000000000)
  directionLo := (57231862584330753123/12500000000000000000)
  directionHi := (91570980134929204997/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree085.table
  base := (3709288466824186889881407982831454754519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-36773373672600246094595436330747599500000000000)
      constant := (818731701721983329257258270123991264939855892762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree085.table
  base := (7418575740841526270479320145893021602161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-36813989328168568585379124528147755750000000000)
      constant := (820530251096048270734428371289242170162001144939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57231862584330753123/12500000000000000000)
  centralHi := (91570980134929204997/20000000000000000000)
  directionLo := (230286082148392964941/50000000000000000000)
  directionHi := (460572164296785929883/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree086.table
  base := (327783929997985258878261836054155747453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-37205753606843347923540657225611757000000000000)
      constant := (838501152558034641518883643103905091823999021175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree086.table
  base := (8194597231618506974923808536425918064169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-37246847093653650678921800578275444500000000000)
      constant := (840342257546170131744989825771458383718195751731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230286082148392964941/50000000000000000000)
  centralHi := (460572164296785929883/100000000000000000000)
  directionLo := (28954593154779997419/6250000000000000000)
  directionHi := (92654698095295991741/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree087.table
  base := (4495409262327483929970982115692841051443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3421648503735131795680534374588719500000000000)
      constant := (78046287379024161512470018693134905423164971974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree087.table
  base := (8990817655395980787230353707313841342203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-37679704859138732772464476628403133250000000000)
      constant := (860393319337752837858904800438431414556223591097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28954593154779997419/6250000000000000000)
  centralHi := (92654698095295991741/20000000000000000000)
  directionLo := (116489789099596826519/25000000000000000000)
  directionHi := (465959156398387306077/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree088.table
  base := (306476171717528512547924374885393375677/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3460955770484504689221009001394552000000000000)
      constant := (79886884307209962575884346989849840862613698976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree088.table
  base := (4903618376524810566819652773009349420449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3464778420420346806000650243502802000000000000)
      constant := (80062130572445301148804524350844278297584346082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116489789099596826519/25000000000000000000)
  centralHi := (465959156398387306077/100000000000000000000)
  directionLo := (468629431304450144353/100000000000000000000)
  directionHi := (234314715652225072177/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree089.table
  base := (1064385493915981532337842712088741373441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-38502893409572653410376319910204229500000000000)
      constant := (899240851039378294556309074715325376250998816590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree089.table
  base := (10643854306021365616884235454109662744777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-38545420390108896959549828728658510750000000000)
      constant := (901212608276932458962081625068046993753669599923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468629431304450144353/100000000000000000000)
  centralHi := (234314715652225072177/50000000000000000000)
  directionLo := (94256915361785089957/20000000000000000000)
  directionHi := (235642288404462724893/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree090.table
  base := (1150067067022155885147721655149963997019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-38935273343815755239321540805068387000000000000)
      constant := (919964532023956170293900830220866640009354538810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree090.table
  base := (718791883123549708198472398454646587033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-38978278155593979053092504778786199500000000000)
      constant := (921980835154148632641343887323005024949830148272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94256915361785089957/20000000000000000000)
  centralHi := (235642288404462724893/50000000000000000000)
  directionLo := (236962423598765732057/50000000000000000000)
  directionHi := (94784969439506292823/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree091.table
  base := (6188842265188692300131999151674376303173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-232944693953010988569625808875340500000000000)
      constant := (5567614025012809228187622248142656677849799966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree091.table
  base := (12377684069453911984614122979419971753493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223477996249231442502103384790000000000000)
      linear := (-21200180699881151773337913302266750000000000)
      constant := (507255576559556988748220186156905445740510973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236962423598765732057/50000000000000000000)
  centralHi := (94784969439506292823/20000000000000000000)
  directionLo := (59568811213959621799/12500000000000000000)
  directionHi := (476550489711676974393/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree092.table
  base := (2654979277309876951348428814224825091157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-39800033212301958897211982594796702000000000000)
      constant := (962127565559695611510336839601986735969251857715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree092.table
  base := (663744799667418134728704116893800016997/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-39843993686564143240177856879041577000000000000)
      constant := (964234453199151887171696618048109718077133394060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59568811213959621799/12500000000000000000)
  centralHi := (476550489711676974393/100000000000000000000)
  directionLo := (479161744818672619359/100000000000000000000)
  directionHi := (2994760905116703871/625000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree093.table
  base := (14192306126493629688236283532144089690669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-40232413146545060726157203489660859500000000000)
      constant := (983566917946221937201228060870318566978568275231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree093.table
  base := (7096152895552189764228747348641450827613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-40276851452049225333720532929169265750000000000)
      constant := (985719844204761102603811217157534681400733013374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479161744818672619359/100000000000000000000)
  centralHi := (2994760905116703871/625000000000000000)
  directionLo := (60219855808595008073/12500000000000000000)
  directionHi := (96351769293752012917/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree094.table
  base := (7564956827772758230007863653098188779671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-40664793080788162555102424384525017000000000000)
      constant := (1005244827323214416271486992828733398908696856858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree094.table
  base := (15129913369501133194753263818609141605019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-40709709217534307427263208979296954500000000000)
      constant := (1007444289778483683062581318219044290103236645881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60219855808595008073/12500000000000000000)
  centralHi := (96351769293752012917/20000000000000000000)
  directionLo := (484342022339736619631/100000000000000000000)
  directionHi := (30271376396233538727/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree095.table
  base := (4021929723468329190291278928783570704207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-113842584529172477518137521549554500000000000)
      constant := (2845322143039052785826555813054256663006483252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree095.table
  base := (16087718649941439277523860433569955513899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-113968329592851494517467825566273250000000000)
      constant := (2851545124286906195799600169745767055112838241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484342022339736619631/100000000000000000000)
  centralHi := (30271376396233538727/6250000000000000000)
  directionLo := (48691149406989923889/10000000000000000000)
  directionHi := (486911494069899238891/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree096.table
  base := (17065721774160581258926140616113982845029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-41529552949274366212992866174253332000000000000)
      constant := (1049316316842696853606162260085523989773316116871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree096.table
  base := (8532860783082150066274309389905855716879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-41575424748504471614348561079552332000000000000)
      constant := (1051610344427561774208995401762617771731483560042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48691149406989923889/10000000000000000000)
  centralHi := (486911494069899238891/100000000000000000000)
  directionLo := (15295858671249451237/3125000000000000000)
  directionHi := (97893495495996487917/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree097.table
  base := (18063922239650444363413775639675608750369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-41961932883517468041938087069117489500000000000)
      constant := (1071709896901921334299307576236027253638013885531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree097.table
  base := (2257990257789379638305860366895018005137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-42008282513989553707891237129680020750000000000)
      constant := (1074051953420965576648995434863516657326147984504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15295858671249451237/3125000000000000000)
  centralHi := (97893495495996487917/20000000000000000000)
  directionLo := (492010182784719112779/100000000000000000000)
  directionHi := (24600509139235955639/5000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree098.table
  base := (9541160121247663267178439926833671746253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3854028437978233624625755269452877000000000000)
      constant := (99485639434787366816447834050515481334134298554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree098.table
  base := (954116004565856068626017047302355289183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-42441140279474635801433913179807709500000000000)
      constant := (1096732616816191532584587350127190933425558442340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492010182784719112779/100000000000000000000)
  centralHi := (24600509139235955639/5000000000000000000)
  directionLo := (2472699073973055797/500000000000000000)
  directionHi := (494539814794611159401/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree099.table
  base := (1257557233897772031103880596447602341951/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3893335704727606518166229896258709500000000000)
      constant := (101564793405259085962313570249884449934231416944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree099.table
  base := (5030228903374636786402550544939313002903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-3897636185905428899543326293630490750000000000)
      constant := (101786575871510527145941533483528724086413936508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2472699073973055797/500000000000000000)
  centralHi := (494539814794611159401/100000000000000000000)
  directionLo := (497056573108458049229/100000000000000000000)
  directionHi := (49705657310845804923/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree100.table
  base := (21179708705268247829585062482256255266649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-43259072686246773528773749753709962000000000000)
      constant := (1140321977904677898036376466491742453153192877251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree100.table
  base := (1058985429771648062152285512003352642607/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-43306855810444799988519265280063087000000000000)
      constant := (1142811106709805982516766827491642537227018301860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497056573108458049229/100000000000000000000)
  centralHi := (49705657310845804923/10000000000000000000)
  directionLo := (62445081537144437721/12500000000000000000)
  directionHi := (499560652297155501769/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree101.table
  base := (11129349551283879152239794265136318348623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-43691452620489875357718970648574119500000000000)
      constant := (1163669785103925117462130809805511565246135093354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree101.table
  base := (22258699008961981274669369107773026499009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-43739713575929882082061941330190775750000000000)
      constant := (1166208933166865022055164922224679212818270940891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62445081537144437721/12500000000000000000)
  centralHi := (499560652297155501769/100000000000000000000)
  directionLo := (502052242079243274711/100000000000000000000)
  directionHi := (62756530259905409339/12500000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree102.table
  base := (23357886910136937618947950136861637929147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-44123832554732977186664191543438277000000000000)
      constant := (1187256149039400705424448397839714525477612622553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree102.table
  base := (2919735853796297649871570028019281220693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4015688303764996743236783398210769500000000000)
      constant := (108167801267443422976301887282889721717696073896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502052242079243274711/100000000000000000000)
  centralHi := (62756530259905409339/12500000000000000000)
  directionLo := (252265763744325146601/50000000000000000000)
  directionHi := (504531527488650293203/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree103.table
  base := (6119318026914280676781478329007857647763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-44556212488976079015609412438302434500000000000)
      constant := (1211081069697468827458490809030586203819474406148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree103.table
  base := (24477272039690249465539305696222603333167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-44605429106900046269147293430446153250000000000)
      constant := (1213721749021443429095661728804959281569597540533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252265763744325146601/50000000000000000000)
  centralHi := (504531527488650293203/100000000000000000000)
  directionLo := (50699868903505685633/10000000000000000000)
  directionHi := (506998689035056856331/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree104.table
  base := (12808427339010595526465536163711954283967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-266204688894788052334642800787968000000000000)
      constant := (7308547615778987637578921047148982340923265914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree104.table
  base := (1601053413757122476782979111950447199587/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-266498738889852830548461357873218000000000000)
      constant := (7324477741978004555171655315925878113272959632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50699868903505685633/10000000000000000000)
  centralHi := (506998689035056856331/100000000000000000000)
  directionLo := (254726951428633615427/50000000000000000000)
  directionHi := (101890780571453446171/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree105.table
  base := (13388317303415440109375642029721303041283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-45420972357462282673499854228030749500000000000)
      constant := (1259446581137278295777869870022440684280653960034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree105.table
  base := (2677663455749894428541159638267022793089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-45471144637870210456232645530701530750000000000)
      constant := (1262190782050904612083096993184121098739504848110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254726951428633615427/50000000000000000000)
  centralHi := (101890780571453446171/20000000000000000000)
  directionLo := (511897340869961417043/100000000000000000000)
  directionHi := (127974335217490354261/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree106.table
  base := (27956611881972638257816428892414439173999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-45853352291705384502445075122894907000000000000)
      constant := (1283987171901227589941661967686731222840231554901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree106.table
  base := (559132236798998433896552666504945556363/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-45904002403355292549775321580829219500000000000)
      constant := (1286783879983326044191576183758412374427732646850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511897340869961417043/100000000000000000000)
  centralHi := (127974335217490354261/25000000000000000000)
  directionLo := (64291146363021511773/12500000000000000000)
  directionHi := (102865834180834418837/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree107.table
  base := (7289196623314935601626476030409652573293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-46285732225948486331390296017759064500000000000)
      constant := (1308766319351660493782270927106527630760387436028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree107.table
  base := (7289196614366616856218653148764638160639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-46336860168840374643317997630956908250000000000)
      constant := (1311616032184835791313622880839085550377679189044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64291146363021511773/12500000000000000000)
  centralHi := (102865834180834418837/20000000000000000000)
  directionLo := (32296847302613224001/6250000000000000000)
  directionHi := (516749556841811584017/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree108.table
  base := (30377158432130337988285478962105699657179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-46718112160191588160335516912623222000000000000)
      constant := (1333784023482831155188129302536240871434233169721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree108.table
  base := (30377158401645715817200237395245082629457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-46769717934325456736860673681084597000000000000)
      constant := (1336687238649794698708782516398065368832545963243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32296847302613224001/6250000000000000000)
  centralHi := (516749556841811584017/100000000000000000000)
  directionLo := (129789664686138495371/25000000000000000000)
  directionHi := (103831731748910796297/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree109.table
  base := (31617727691392665098513097692550207896037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4286408372221335453570976164317034500000000000)
      constant := (123549116753628471934453792274853217227279321333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree109.table
  base := (3952215958178946589016204848127162786251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-47202575699810538830403349731212285750000000000)
      constant := (1361997499373467428642591445564056893182334578792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129789664686138495371/25000000000000000000)
  centralHi := (103831731748910796297/20000000000000000000)
  directionLo := (260778316488679638837/50000000000000000000)
  directionHi := (20862265319094371107/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree110.table
  base := (32878494265010104042143227932327809069599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4325715638970708347111450791122867000000000000)
      constant := (125866827433532312055830254802985741678527165391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree110.table
  base := (3287849424290316799244389014767560373513/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4330493951390510993086002343758179500000000000)
      constant := (126140619486534590100023105809410875752026546170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260778316488679638837/50000000000000000000)
  centralHi := (20862265319094371107/4000000000000000000)
  directionLo := (52394363232690923329/10000000000000000000)
  directionHi := (523943632326909233291/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree111.table
  base := (34159458147919821042670015371383636998191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-48015251962920893647171179597215694500000000000)
      constant := (1410268475916260216508973263642990667687098981909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree111.table
  base := (34159458129096413070024572591659711159407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-48068291230780703017488701831467663250000000000)
      constant := (1413335183581702491194372988616746379569679378293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52394363232690923329/10000000000000000000)
  centralHi := (523943632326909233291/100000000000000000000)
  directionLo := (526319806115208855647/100000000000000000000)
  directionHi := (16447493941100276739/3125000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree112.table
  base := (7092123867175953332234696674712634713573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-48447631897163995476116400492079852000000000000)
      constant := (1436240406729280707827103340053281256218220633635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree112.table
  base := (35460619319853487366724483610091550358283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-48501148996265785111031377881595352000000000000)
      constant := (1439362607060143119692773910248573763353893363017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526319806115208855647/100000000000000000000)
  centralHi := (16447493941100276739/3125000000000000000)
  directionLo := (264342650154296249579/50000000000000000000)
  directionHi := (528685300308592499159/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree113.table
  base := (9195494456334899675477954672253371886567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-48880011831407097305061621386944009500000000000)
      constant := (1462450894205534275471302896933551871760062908532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree113.table
  base := (36781977811695886891901828222318589265977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4448546069250078836779459448338458250000000000)
      constant := (133239007707715268731440110075389168273465490793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264342650154296249579/50000000000000000000)
  centralHi := (528685300308592499159/100000000000000000000)
  directionLo := (53104025762235976741/10000000000000000000)
  directionHi := (531040257622359767411/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree114.table
  base := (38123533613331792800430632196861803313769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-136599423173546257988938621279247000000000000)
      constant := (4124376560507006694759310133515717217360296571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree114.table
  base := (7624706720343470123670196536196886083521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-136750317249961078388134986099309500000000000)
      constant := (4133336888515032164499939677195680087396327695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53104025762235976741/10000000000000000000)
  centralHi := (531040257622359767411/100000000000000000000)
  directionLo := (133346204405313367457/25000000000000000000)
  directionHi := (533384817621253469829/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree115.table
  base := (39485286697379787362049628519599899014849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-49744771699893300962952063176672324500000000000)
      constant := (1515587539140104113827899172302596997160216149051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree115.table
  base := (39485286687493556269201916004992158463429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-49799722292721031391659406031978418250000000000)
      constant := (1518879202965692125452999747242269586185461238471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133346204405313367457/25000000000000000000)
  centralHi := (533384817621253469829/100000000000000000000)
  directionLo := (107143823363195961877/20000000000000000000)
  directionHi := (267859558407989904693/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree116.table
  base := (40867237075420501895535879549546401343387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-50177151634136402791897284071536482000000000000)
      constant := (1542513696595373835276081612423684254895145672313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree116.table
  base := (40867237067005963025271764501924295326913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-50232580058206113485202082082106107000000000000)
      constant := (1545862843418809857526192981512050397794595987387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107143823363195961877/20000000000000000000)
  centralHi := (267859558407989904693/50000000000000000000)
  directionLo := (538043288755959687183/100000000000000000000)
  directionHi := (33627705547247480449/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree117.table
  base := (8453876949147796658097518234817949983747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-299464683836565116099659792700595500000000000)
      constant := (9288037933181583892516099082457137178177296685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree117.table
  base := (10567346184644397153452990790238371683427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-299795490081012991590205669421501750000000000)
      constant := (9308198450367777434779873591992791241132054468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538043288755959687183/100000000000000000000)
  centralHi := (33627705547247480449/6250000000000000000)
  directionLo := (27017873205924472383/5000000000000000000)
  directionHi := (540357464118489447661/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree118.table
  base := (21845864853456642609444057436862783578843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-51041911502622606449787725861264797000000000000)
      constant := (1597081681476091374746530925032521913518955916914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree118.table
  base := (8738345940163770823064310562009819252093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-51098295589176277672287434182361484500000000000)
      constant := (1600547287044793167284518539647072963982551801035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27017873205924472383/5000000000000000000)
  centralHi := (540357464118489447661/100000000000000000000)
  directionLo := (271330885397239750851/50000000000000000000)
  directionHi := (542661770794479501703/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree119.table
  base := (45134271957767981729267418771176170771597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-51474291436865708278732946756128954500000000000)
      constant := (1624723508899796098829406565792672270809897975103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree119.table
  base := (22567135976290960819846906657412546559523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-51531153354661359765830110232489173250000000000)
      constant := (1628248090215955887086139959537457799612411151554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271330885397239750851/50000000000000000000)
  centralHi := (542661770794479501703/100000000000000000000)
  directionLo := (136239083492732501399/25000000000000000000)
  directionHi := (544956333970930005597/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree120.table
  base := (23298505748667482896308627892979121753427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4718788306464437282516197059181192000000000000)
      constant := (150236717543468377674980660146203816478109655686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree120.table
  base := (23298505746461098112923951619036535689507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-51964011120146441859372786282616862000000000000)
      constant := (1656187947625008629148876505110267102629384916386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136239083492732501399/25000000000000000000)
  centralHi := (544956333970930005597/100000000000000000000)
  directionLo := (68405159526286762103/12500000000000000000)
  directionHi := (21889651048411763873/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree121.table
  base := (48079948324820394265046478844297095491721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4758095573213810176056671685987024500000000000)
      constant := (152792984882784254017513709779015265842604406489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree121.table
  base := (600999354013323387987820973891728088559/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4763351716875593086628678393885868250000000000)
      constant := (153124259933766553861793529112422321452329182480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68405159526286762103/12500000000000000000)
  centralHi := (21889651048411763873/4000000000000000000)
  directionLo := (68689589690858881493/12500000000000000000)
  directionHi := (109903343505374210389/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree122.table
  base := (9916616487915363707909601679851047783357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-52771431239595013765568609440721427000000000000)
      constant := (1709080331096785516020283359598579898706815496715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree122.table
  base := (49583082436382570191788671679871539206843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-52829726651116606046458138382872239500000000000)
      constant := (1712784825154803232451012838054156646121423130457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68689589690858881493/12500000000000000000)
  centralHi := (109903343505374210389/20000000000000000000)
  directionLo := (551782775460364099373/100000000000000000000)
  directionHi := (275891387730182049687/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree123.table
  base := (51106413841079690204391459853792162077239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-53203811173838115594513830335585584500000000000)
      constant := (1737676385136276295993121068323788614209123015661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree123.table
  base := (798537716224410802704268768304230908969/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-53262584416601688140000814432999928250000000000)
      constant := (1741441845274779787021776031715398929269616463584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551782775460364099373/100000000000000000000)
  centralHi := (275891387730182049687/50000000000000000000)
  directionLo := (110807913029346091137/20000000000000000000)
  directionHi := (277019782573365227843/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree124.table
  base := (52649942528907557642909113733337746947069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-53636191108081217423459051230449742000000000000)
      constant := (1766510995828816298352669843873129539138431058831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree124.table
  base := (52649942526595975215972140135641019822057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-4881403834735160930322135498466147000000000000)
      constant := (160939810875553385169086035972799225353323875513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110807913029346091137/20000000000000000000)
  centralHi := (277019782573365227843/50000000000000000000)
  directionLo := (55628719938644442591/10000000000000000000)
  directionHi := (556287199386444425911/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree125.table
  base := (54213668502725376356486123028899020686989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54068571042324319252404272125313899500000000000)
      constant := (1795584163174180675070953761033714498415267630911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree125.table
  base := (13553417125189783395390922496127386644839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54128299947571852327086166533255305750000000000)
      constant := (1799473048223507818299981649899811502082671732244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55628719938644442591/10000000000000000000)
  centralHi := (556287199386444425911/100000000000000000000)
  directionLo := (558525788710288086221/100000000000000000000)
  directionHi := (279262894355144043111/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree126.table
  base := (11159518352454089191208433315046483464297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54500950976567421081349493020178057000000000000)
      constant := (1824895887172193128179561405351869700157031262015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree126.table
  base := (55797591760598057730871758885702902356939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54561157713056934420628842583382994500000000000)
      constant := (1828847231051871267660863678059845004850089405961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558525788710288086221/100000000000000000000)
  centralHi := (279262894355144043111/50000000000000000000)
  directionLo := (28037772072138906201/5000000000000000000)
  directionHi := (560755441442778124021/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree127.table
  base := (14350428076835140712989526493664824894831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54933330910810522910294713915042214500000000000)
      constant := (1854446167822717959051702962668051408569634757076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree127.table
  base := (28700856152959101135673355745524329969293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-54994015478542016514171518633510683250000000000)
      constant := (1858460468116047025724197812448368819456437626014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28037772072138906201/5000000000000000000)
  centralHi := (560755441442778124021/100000000000000000000)
  directionLo := (281488131881665910033/50000000000000000000)
  directionHi := (562976263763331820067/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree128.table
  base := (59026030137784041876358918715447877885003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-55365710845053624739239934809906372000000000000)
      constant := (1884235005125653371922902673249658931400747628297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree128.table
  base := (59026030136574403967630552503078304862769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-55426873244027098607714194683638372000000000000)
      constant := (1888312759415937673587898537779247123315099413131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281488131881665910033/50000000000000000000)
  centralHi := (562976263763331820067/100000000000000000000)
  directionLo := (565188359765269896457/100000000000000000000)
  directionHi := (282594179882634948229/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree129.table
  base := (12134109050698262849968970681331705912207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-55798090779296726568185155704770529500000000000)
      constant := (1914262399080925835294874143337984078811131027465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree129.table
  base := (60670545252462647829264464310031755574889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-55859731009512180701256870733766060750000000000)
      constant := (1918404104951473406895883932012045337454864933011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565188359765269896457/100000000000000000000)
  centralHi := (282594179882634948229/50000000000000000000)
  directionLo := (113478366302549800233/20000000000000000000)
  directionHi := (283695915756374500583/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree130.table
  base := (15583814413596963755625829280770758174967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-332724678778342179864676784613223000000000000)
      constant := (11506084909399321512119857880079955847851175828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree130.table
  base := (62335257653513137874768274264894953588123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-333092241272173152631949980969785500000000000)
      constant := (11530973400725487488963187176115532391948436433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113478366302549800233/20000000000000000000)
  centralHi := (283695915756374500583/50000000000000000000)
  directionLo := (142396694773927983511/25000000000000000000)
  directionHi := (113917355819142386809/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree131.table
  base := (8002520917553528962160949547452711882631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5151168240707539111461417954045349500000000000)
      constant := (179548441540754671179973876005737035587729477432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree131.table
  base := (64020167339684467925154770970085672257507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-56725446540482344888342222834021438250000000000)
      constant := (1979303958729311822159270501451979998949153190193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142396694773927983511/25000000000000000000)
  centralHi := (113917355819142386809/20000000000000000000)
  directionLo := (571773300682939322241/100000000000000000000)
  directionHi := (285886650341469661121/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree132.table
  base := (65725274311591098297337250792255333268967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5190475507456912005001892580851182000000000000)
      constant := (182343265532759968393229003785953977127406407703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree132.table
  base := (65725274310958719799770122144840952434563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5196209482360675180171354444013557000000000000)
      constant := (182737496997415881054203721080692970042080254067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571773300682939322241/100000000000000000000)
  centralHi := (285886650341469661121/50000000000000000000)
  directionLo := (143487873143320576789/25000000000000000000)
  directionHi := (573951492573282307157/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree133.table
  base := (16862644641968746652056658030627498731297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-159356261817920038459739721008939500000000000)
      constant := (5641987649375787142017845873610747861815924492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree133.table
  base := (13490115713467468660177321293055861086223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-159532304907070662258802146632345750000000000)
      constant := (5654182907062041459574917030519992924108942785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143487873143320576789/25000000000000000000)
  centralHi := (573951492573282307157/100000000000000000000)
  directionLo := (576121449245151894433/100000000000000000000)
  directionHi := (288060724622575947217/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree134.table
  base := (6919608010929476950528573073901487010231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-57959990450512235712911260179091317000000000000)
      constant := (2067977718641209881980243673453462761435790138690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree134.table
  base := (34598040054418847581629778777030751741639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-58024019836937591168970250984404504500000000000)
      constant := (2072446646162790296177520419481098345957374382522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576121449245151894433/100000000000000000000)
  centralHi := (288060724622575947217/50000000000000000000)
  directionLo := (578283263404336928003/100000000000000000000)
  directionHi := (144570815851084232001/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree135.table
  base := (8870222366984836354366094412265327481029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-58392370384755337541856481073955474500000000000)
      constant := (2099436452510030777878007709900511712838778646968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree135.table
  base := (14192355787098026674226159138009026682541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5314261600220243023864811548593835750000000000)
      constant := (191270210646525004783821249784098765380313219345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578283263404336928003/100000000000000000000)
  centralHi := (144570815851084232001/25000000000000000000)
  directionLo := (580437026030219164793/100000000000000000000)
  directionHi := (290218513015109582397/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree136.table
  base := (72747675047665872822650700133486023358987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-58824750318998439370801701968819632000000000000)
      constant := (2131133743031148100848141934916946878790192816713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree136.table
  base := (36373837523667789732477914072357948819153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-58889735367907755356055603084659882000000000000)
      constant := (2135737042296378698644963182924068448689169518294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580437026030219164793/100000000000000000000)
  centralHi := (290218513015109582397/50000000000000000000)
  directionLo := (145645706605112658923/25000000000000000000)
  directionHi := (582582826420450635693/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree137.table
  base := (14910753688940845181210363477904487489861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-59257130253241541199746922863683789500000000000)
      constant := (2163069590204594003537409440116634603031041136195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree137.table
  base := (14910753688884695028685213753058204534501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-59322593133392837449598279134787570750000000000)
      constant := (2167740821716634414520858834519498067969807932995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145645706605112658923/25000000000000000000)
  centralHi := (582582826420450635693/100000000000000000000)
  directionLo := (584720752234155368371/100000000000000000000)
  directionHi := (146180188058538842093/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree138.table
  base := (76380059127048697641485768983014442793463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-59689510187484643028692143758547947000000000000)
      constant := (2195243994030405361195931611658265758669250225837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree138.table
  base := (76380059126810071009666944741603989354333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-59755450898877919543140955184915259500000000000)
      constant := (2199983655372579949973227573473045336182953521967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584720752234155368371/100000000000000000000)
  centralHi := (146180188058538842093/25000000000000000000)
  directionLo := (586850889533714607607/100000000000000000000)
  directionHi := (73356361191714325951/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree139.table
  base := (39113273547379903623704271670593262598133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-60121890121727744857637364653412104500000000000)
      constant := (2227656954508622788210695044919362270903938916334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree139.table
  base := (19556636773639248762089455106748119943483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-60188308664363001636683631235042948250000000000)
      constant := (2232465543264256663480959736522870818441618491268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586850889533714607607/100000000000000000000)
  centralHi := (73356361191714325951/12500000000000000000)
  directionLo := (117794664565038377657/20000000000000000000)
  directionHi := (294486661412595944143/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree140.table
  base := (80093232347902420712901939909271242332101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-60554270055970846686582585548276262000000000000)
      constant := (2260308471639289816082106546425820263957830648999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree140.table
  base := (80093232347730056635189967360785360909177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-60621166429848083730226307285170637000000000000)
      constant := (2265186485391708719650272360307746578045787775523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117794664565038377657/20000000000000000000)
  centralHi := (294486661412595944143/50000000000000000000)
  directionLo := (147772033774362921381/25000000000000000000)
  directionHi := (23643525403898067421/4000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree141.table
  base := (40990057443272364229034330643389469900437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-60986649990213948515527806443140419500000000000)
      constant := (2293198545422452207332906619789468531252676740526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree141.table
  base := (81980114886398248809686635729025810997143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-61054024195333165823768983335298325750000000000)
      constant := (2298146481754982419640996458504276005867184170157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147772033774362921381/25000000000000000000)
  centralHi := (23643525403898067421/4000000000000000000)
  directionLo := (593195407860022876351/100000000000000000000)
  directionHi := (9268678247812857443/1562500000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree142.table
  base := (83887194710757393488186073909251876640637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5583548174950640940406638848909507000000000000)
      constant := (211484288714377943985024900031621186116968622733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree142.table
  base := (41943597355316458693932455896481862092051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-61486881960818247917311659385426014500000000000)
      constant := (2331345532354125643558915281685297644617476668098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593195407860022876351/100000000000000000000)
  centralHi := (9268678247812857443/1562500000000000000)
  directionLo := (297647610589877944781/50000000000000000000)
  directionHi := (595295221179755889563/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree143.table
  base := (85814471820612843007928842792272176920781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223477996249231442502103384790000000000000)
      linear := (-33271333974556294875426706956895500000000000)
      constant := (1269335321649517994305453658482090349618401941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree143.table
  base := (8581447182050707042202840306142409131451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (223477996249231442502103384790000000000000)
      linear := (-33308090223939392152154026592551750000000000)
      constant := (1272072962447115323848801360164807120402038110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297647610589877944781/50000000000000000000)
  centralHi := (595295221179755889563/100000000000000000000)
  directionLo := (597387653716320186893/100000000000000000000)
  directionHi := (298693826858160093447/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree144.table
  base := (87761946216184680700995633615991571433629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-62283789792943254002363469127732892000000000000)
      constant := (2393300106687391305427126462939871415597536988271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree144.table
  base := (87761946216094805674152869248675214474757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-62352597491788412104397011485681392000000000000)
      constant := (2398460796260217377002979969455998125758794947943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597387653716320186893/100000000000000000000)
  centralHi := (298693826858160093447/50000000000000000000)
  directionLo := (599472782756586602121/100000000000000000000)
  directionHi := (299736391378293301061/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree145.table
  base := (8972961789754720045677241829207361679507/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-62716169727186355831308690022597049500000000000)
      constant := (2427144407081019304430011272176774915438804681930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree145.table
  base := (44864808948735418638759522439187982726127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-62785455257273494197939687535809080750000000000)
      constant := (2432377009567265754043220572072255656609354707146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599472782756586602121/100000000000000000000)
  centralHi := (299736391378293301061/50000000000000000000)
  directionLo := (601550684247937058177/100000000000000000000)
  directionHi := (300775342123968529089/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree146.table
  base := (18343497372954997068550155430619346052689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-63148549661429457660253910917461207000000000000)
      constant := (2461227264127388001044503310898529502708067676055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree146.table
  base := (91717486864710105720252832093390160730623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-5747119365705325117407487598721524500000000000)
      constant := (224230207010034800967480394654302072159764578607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601550684247937058177/100000000000000000000)
  centralHi := (300775342123968529089/50000000000000000000)
  directionLo := (301810716415271139763/50000000000000000000)
  directionHi := (603621432830542279527/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree147.table
  base := (23431388279485644541661553359544888495691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-63580929595672559489199131812325364500000000000)
      constant := (2495548677826547420874317645613404459029528937636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree147.table
  base := (46862776558943728890067395772128359932749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-63651170788243658385025039636064458250000000000)
      constant := (2500926598889618776397893033303215555577828342302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301810716415271139763/50000000000000000000)
  centralHi := (603621432830542279527/100000000000000000000)
  directionLo := (605685101868646311731/100000000000000000000)
  directionHi := (151421275467161577933/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree148.table
  base := (23938454164281053029810252578874222970253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64013309529915661318144352707189522000000000000)
      constant := (2530108648178547381739555075773278727144455272188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree148.table
  base := (95753816657077385144895013374110520702441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64084028553728740478567715686192147000000000000)
      constant := (2535559974905023642607190624154901615457887452659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605685101868646311731/100000000000000000000)
  centralHi := (151421275467161577933/25000000000000000000)
  directionLo := (30387088174044747341/5000000000000000000)
  directionHi := (607741763480894946821/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree149.table
  base := (1956045549647871836002201521026449749309/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64445689464158763147089573602053679500000000000)
      constant := (2564907175183437346723285722740740350046826029550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree149.table
  base := (3056321171323556632104546250573066744857/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64516886319213822572110391736319835750000000000)
      constant := (2570432405156647019869690822352786466878829710976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30387088174044747341/5000000000000000000)
  centralHi := (607741763480894946821/100000000000000000000)
  directionLo := (609791488569743526387/100000000000000000000)
  directionHi := (152447872142435881597/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree150.table
  base := (99870935593823716456064757252770061033467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64878069398401864976034794496917837000000000000)
      constant := (2599944258841266305547045434412476738314498670233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree150.table
  base := (6241933474611870323855807864687157633181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-64949744084698904665653067786447524500000000000)
      constant := (2605543889644538023340295613117826433338772174704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609791488569743526387/100000000000000000000)
  centralHi := (152447872142435881597/25000000000000000000)
  directionLo := (15295858671249451237/2500000000000000000)
  directionHi := (611834346849978049481/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree151.table
  base := (10195979099148673855066012291501180132589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-65310449332644966804980015391781994500000000000)
      constant := (2635219899152082679656973554036078952639253453110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree151.table
  base := (50979895495729017694865536054636372697289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-65382601850183986759195743836575213250000000000)
      constant := (2640894428368745181115015381010793296106868401222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15295858671249451237/2500000000000000000)
  centralHi := (611834346849978049481/100000000000000000000)
  directionLo := (122774081375276408903/20000000000000000000)
  directionHi := (153467601719095511129/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree152.table
  base := (5203442183772692593491509829051396098621/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-182113100462293818930540820738632000000000000)
      constant := (7398155390902864950503093127083704906946728780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree152.table
  base := (104068843675429471750039633026585155225283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18590000000000000000000000000000000000000000
      center := (330902)
      previous := (165451)
      next := (165451)
      square := (1150818822790363577870942361010000000000000)
      linear := (-182314292564180246129469307165382000000000000)
      constant := (7414083161577053634200437877124108303563801097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122774081375276408903/20000000000000000000)
  centralHi := (153467601719095511129/25000000000000000000)
  directionLo := (615899736070580269483/100000000000000000000)
  directionHi := (153974934017645067371/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree153.table
  base := (106198093645795204285180489590136844433117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6015928109193742769351859743773664500000000000)
      constant := (246044259066624371285223746908199777085770035053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree153.table
  base := (106198093645774497000787057285137917396951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-66248317381154150946281095936830590750000000000)
      constant := (2712312668526298719087645798763773297422488919149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615899736070580269483/100000000000000000000)
  centralHi := (153974934017645067371/25000000000000000000)
  directionLo := (308961200373544489201/50000000000000000000)
  directionHi := (617922400747088978403/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree154.table
  base := (54173770451289915534644942596991810830379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6055235375943115662892334370579497000000000000)
      constant := (249316196363902774561536341940574084148901184822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree154.table
  base := (10834754090256224406337095843902986728463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6061925013330839367256706544268934500000000000)
      constant := (249852760905430786143026870312295097266917991670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308961200373544489201/50000000000000000000)
  centralHi := (617922400747088978403/100000000000000000000)
  directionLo := (991901545821761969/160000000000000000)
  directionHi := (309969233069300615313/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree155.table
  base := (110517185445875605309009834909665047785703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-67039969069617374120760898971238624500000000000)
      constant := (2778708026926167104810645177207241745935187497597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree155.table
  base := (110517185445860669031975725878338591351871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-67114032912124315133366448037085968250000000000)
      constant := (2784687125629681752670158447191513093325461776229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (991901545821761969/160000000000000000)
  centralHi := (309969233069300615313/50000000000000000000)
  directionLo := (310973998210267259791/50000000000000000000)
  directionHi := (621947996420534519583/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree156.table
  base := (563535136378746012560729672730535876341/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-399244668661896307394710768438478000000000000)
      constant := (16657848819542145466895327166359482092990022200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree156.table
  base := (112707027275736517971775480465351687453579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-399685743654493474715438604066353000000000000)
      constant := (16693686009089780044945720161947542675878162209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310973998210267259791/50000000000000000000)
  centralHi := (621947996420534519583/100000000000000000000)
  directionLo := (155987763683716713861/25000000000000000000)
  directionHi := (124790210946973371089/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree157.table
  base := (114917066392266076966053409643332266019677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-67904728938103577778651340760966939500000000000)
      constant := (2851883430732340883767684907573530508924789215023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree157.table
  base := (14364633299031913142706133491453729901653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6179977131190407210950163648849213250000000000)
      constant := (259819799970841439900356335314519597258997083016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155987763683716713861/25000000000000000000)
  centralHi := (124790210946973371089/20000000000000000000)
  directionLo := (312973851606643174497/50000000000000000000)
  directionHi := (125189540642657269799/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree158.table
  base := (3660853212359076493658263690214115833241/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-68337108872346679607596561655831097000000000000)
      constant := (2888828967615365101789231424830364657615310459488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree158.table
  base := (5857365139774065031956782986365477386911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-68412606208579561413994476187469034500000000000)
      constant := (2895041718058973918192625830884270821958821703780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312973851606643174497/50000000000000000000)
  centralHi := (125189540642657269799/20000000000000000000)
  directionLo := (627938002999678308591/100000000000000000000)
  directionHi := (39246125187479894287/6250000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree159.table
  base := (932794816292853851630270215999613346151/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-68769488806589781436541782550695254500000000000)
      constant := (2926013061151737502445117714920996519455789513472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree159.table
  base := (29849434121369381446777132869608530639877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-68845463974064643507537152237596723250000000000)
      constant := (2932304690675369359008704067042162507535875759292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627938002999678308591/100000000000000000000)
  centralHi := (39246125187479894287/6250000000000000000)
  directionLo := (157480503567993218953/25000000000000000000)
  directionHi := (629922014271972875813/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree160.table
  base := (760427296639452187835327888468658252371/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-69201868740832883265487003445559412000000000000)
      constant := (2963435711341499517678159335106032413521268116640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree160.table
  base := (30417091865576438713174571319825390968479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-69278321739549725601079828287724412000000000000)
      constant := (2969806717528483618001051476868271920214221153684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157480503567993218953/25000000000000000000)
  centralHi := (629922014271972875813/100000000000000000000)
  directionLo := (126379959252675057097/20000000000000000000)
  directionHi := (315949898131687642743/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree161.table
  base := (123959195726032121728804756742829112839287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-69634248675075985094432224340423569500000000000)
      constant := (3001096918184691750854790461683790455078582666413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree161.table
  base := (3873724866438328809915612913023452589427/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-69711179505034807694622504337852100750000000000)
      constant := (3007547798618357319531157956827384365118292348736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126379959252675057097/20000000000000000000)
  centralHi := (315949898131687642743/50000000000000000000)
  directionLo := (633871407282999939997/100000000000000000000)
  directionHi := (316935703641499969999/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree162.table
  base := (126270221276703886377865762952252098253259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-70066628609319086923377445235287727000000000000)
      constant := (3038996681681353983612212833972989993010663861641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree162.table
  base := (126270221276699131908749232509725607672129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-70144037270519889788165180387979789500000000000)
      constant := (3045527933945030263076789800008416430364408099771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633871407282999939997/100000000000000000000)
  centralHi := (316935703641499969999/50000000000000000000)
  directionLo := (317918452367964316757/50000000000000000000)
  directionHi := (127167380947185726703/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree163.table
  base := (32150361028596427888413705565616472957339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-70499008543562188752322666130151884500000000000)
      constant := (3077135001831525185027055959220988463072038982244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree163.table
  base := (32150361028595418742154979748286158505711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-70576895036004971881707856438107478250000000000)
      constant := (3083747123508541432873866354701405546630909085556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317918452367964316757/50000000000000000000)
  centralHi := (127167380947185726703/20000000000000000000)
  directionLo := (637796345142712447093/100000000000000000000)
  directionHi := (318898172571356223547/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree164.table
  base := (130952864239134470430124457177288967970063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6448308043436844598297080638637822000000000000)
      constant := (283228352603203956602680563757052358146885573567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree164.table
  base := (13095286423913104346380506235728710282731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-71009752801490053975250532488235167000000000000)
      constant := (3122205367308929009332917407834108623545304913690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637796345142712447093/100000000000000000000)
  centralHi := (318898172571356223547/50000000000000000000)
  directionLo := (639749784158336058339/100000000000000000000)
  directionHi := (31987489207916802917/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree165.table
  base := (133324481651005860372312274611366912026297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6487615310186217491837555265443654500000000000)
      constant := (286738846553867852260498448477778560029562353673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree165.table
  base := (133324481651002951066192094337877194877337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6494782778815921460799382594396623250000000000)
      constant := (287354787758748216531221176632448947555708953033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639749784158336058339/100000000000000000000)
  centralHi := (31987489207916802917/5000000000000000000)
  directionLo := (641697276590662467519/100000000000000000000)
  directionHi := (2005303989345820211/312500000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree166.table
  base := (135716296350054423170975517126097686743647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-71796148346291494239158328814744357000000000000)
      constant := (3192981302203470344676281549730664736600974758053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree166.table
  base := (135716296350051953420634086790463406011119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-71875468332460218162335884588490544500000000000)
      constant := (3199839017620482162644118211739081685341905949781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641697276590662467519/100000000000000000000)
  centralHi := (2005303989345820211/312500000000000000)
  directionLo := (128727775283675086777/20000000000000000000)
  directionHi := (321819438209187716943/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree167.table
  base := (69064154168166783265875480828356196523031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-72228528280534596068103549709608514500000000000)
      constant := (3232073848968051273919727186117334325042069162138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree167.table
  base := (138128308336331470002488320448733560069797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-72308326097945300255878560638618233250000000000)
      constant := (3239014424131720201491466009923635575124593196903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128727775283675086777/20000000000000000000)
  centralHi := (321819438209187716943/50000000000000000000)
  directionLo := (322787318404218119913/50000000000000000000)
  directionHi := (645574636808436239827/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree168.table
  base := (17570064701236948309813774441844256050071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6710990000000000000000000000000000000000000000
      center := (119455622)
      previous := (59727811)
      next := (59727811)
      square := (415445595027321251611410192324610000000000000)
      linear := (-72660908214777697897048770604472672000000000000)
      constant := (3271404952386324258405144040802184113127572784232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree168.table
  base := (5622420704395752273364484136402099122597/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37767781366120113782855472029510000000000000)
      linear := (-6612834896675489304492839698976902000000000000)
      constant := (298038989534543600082252209510675775134263009325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell110.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322787318404218119913/50000000000000000000)
  centralHi := (645574636808436239827/100000000000000000000)
  directionLo := (323752305066535377297/50000000000000000000)
  directionHi := (129500922026614150919/20000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree169.table
  base := (71506462085395845194625486939986928989181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-432504663603673371159727760351105500000000000)
      constant := (19591565754191264280193485380167597721282075502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 22647
  qDenominator := 43472
  table := BinomialMassData.Q22647_43472.Degree169.table
  base := (35753231042697544946731267459372661657863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (706838)
      previous := (353419)
      next := (353419)
      square := (2458257958741545867523137232690000000000000)
      linear := (-432982494845653635757182915614636750000000000)
      constant := (19633623667841980661562940478625313490585995892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22647_43472.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell110.Kernel169
