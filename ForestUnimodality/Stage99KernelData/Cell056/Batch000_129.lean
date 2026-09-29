import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell056.Parameters
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch100_149
import ForestUnimodality.BinomialMassData.Q131_264.Batch000_049
import ForestUnimodality.BinomialMassData.Q131_264.Batch050_099
import ForestUnimodality.BinomialMassData.Q131_264.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree000.table
  base := (2795806587102302667224407159/50000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (105492666697755629878763272500000000000)
      linear := (644844304491349283852547062500000000)
      constant := (69895164677557566680610178975000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree000.table
  base := (2795806587102302667224407159/50000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (105492666697755629878763272500000000000)
      linear := (644844304491349283852547062500000000)
      constant := (69895164677557566680610178975000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree001.table
  base := (15836285885048521624390989151212384115779/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-678113155515536937835148304023625000000000)
      constant := (258852503100947749889068769059369169531249965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree001.table
  base := (316108594056116678406541310746217379285277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-100719079187562948996762651558500000000000)
      constant := (38273974024648085525257008322955677893518517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24998724587403195307/50000000000000000000)
  directionHi := (9999489834961278123/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree002.table
  base := (187137155129526391166820020083468815044383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-5441758894866481407563956602214500000000000)
      constant := (614062139918890906604944219099331618749999261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree002.table
  base := (186479302758010830943876459446273949724517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-606187102985620572300883706020500000000000)
      constant := (67991855068739084958049334491592068749999671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/50000000000000000000)
  centralHi := (9999489834961278123/20000000000000000000)
  directionLo := (7070707070707070707/10000000000000000000)
  directionHi := (70707070707070707071/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree003.table
  base := (23296412155527360524877209898521938597503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-302632043247067224584715555123500000000000)
      constant := (14318547291428229789147975142981272851489315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree003.table
  base := (115946215278970396923747551698977980972633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-303405656136184099203826485788500000000000)
      constant := (14254857784762669038999104300180835697688593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7070707070707070707/10000000000000000000)
  centralHi := (70707070707070707071/100000000000000000000)
  directionLo := (86598122219607306501/100000000000000000000)
  directionHi := (43299061109803653251/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree004.table
  base := (76819198413261557890935869465467040338507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-10900371440475148720010683374454500000000000)
      constant := (261741904482729856658804005685438820785902369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree004.table
  base := (76420478315777984421972712184166333701509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-404748944610494674307358402903500000000000)
      constant := (9647941060507703261378979818166376377882589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86598122219607306501/100000000000000000000)
  centralHi := (43299061109803653251/50000000000000000000)
  directionLo := (24998724587403195307/25000000000000000000)
  directionHi := (99994898349612781229/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree005.table
  base := (10727352129333636171505350487794414903461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-13629677713279482376234046760574500000000000)
      constant := (192075448019137864212454358625619267448035435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree005.table
  base := (26673900749678935167891099752472342751437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-759138349627207874116335480027750000000000)
      constant := (10623198573234952736581399013194647918771631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/25000000000000000000)
  centralHi := (99994898349612781229/100000000000000000000)
  directionLo := (111797695056457855171/100000000000000000000)
  directionHi := (27949423764114463793/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree006.table
  base := (1967578695616450817655720685249814067681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-454416221835661556457150281852625000000000)
      constant := (4245199428866871597892908598321662532841015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree006.table
  base := (39140311471892323022555691478452439247181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-607435521559115824514422237133500000000000)
      constant := (5639299073413519199267903887944870148908901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111797695056457855171/100000000000000000000)
  centralHi := (27949423764114463793/25000000000000000000)
  directionLo := (30617059729752881451/25000000000000000000)
  directionHi := (24493647783802305161/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree007.table
  base := (14993713866724657536141952110947680239067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-9544145129444074844340386766407250000000000)
      constant := (65503409557624975306542209954134321341031889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree007.table
  base := (29828161704591867203761689572544565825849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-708778810033426399617954154248500000000000)
      constant := (4839089704294828877317582133222142464927729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30617059729752881451/25000000000000000000)
  centralHi := (24493647783802305161/20000000000000000000)
  directionLo := (16535102088016155113/12500000000000000000)
  directionHi := (26456163340825848181/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree008.table
  base := (5859519135343655861605669341809733367481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-5454399132923120836226034229733625000000000)
      constant := (29933315693617870917654074979051398911560427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree008.table
  base := (11656432277942883738574066077359218782967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-1215183147761605462082229107045250000000000)
      constant := (6641380905255757812296201930643146418217021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535102088016155113/12500000000000000000)
  centralHi := (26456163340825848181/20000000000000000000)
  directionLo := (141414141414141414141/100000000000000000000)
  directionHi := (70707070707070707071/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree009.table
  base := (371444916768357080606594650922346590131/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-454572274157348462983842598241750000000000)
      constant := (2135382159869041889134605196663348435146275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree009.table
  base := (3693883606267398999271142981899993798513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-911465386982047549825017988478500000000000)
      constant := (4268666529713667701498085527392371248100365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141414141414141414141/100000000000000000000)
  centralHi := (70707070707070707071/50000000000000000000)
  directionLo := (74996173762209585921/50000000000000000000)
  directionHi := (149992347524419171843/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree010.table
  base := (14770017186951529996233560041955951152621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-27276209077301150657350863691174500000000000)
      constant := (115713667154891318844712039775065092415612807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree010.table
  base := (7341142981200928123654850930080944609469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-506404337728179062464274952796750000000000)
      constant := (2143923803265264721008195900464481797745749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74996173762209585921/50000000000000000000)
  centralHi := (149992347524419171843/100000000000000000000)
  directionLo := (79052908295447110479/50000000000000000000)
  directionHi := (158105816590894220959/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree011.table
  base := (467276280607391595558915335458397199427/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3024)
      previous := (1512)
      next := (1512)
      square := (22786416006715216053812866860000000000000)
      linear := (-247979465703351110029539066754500000000000)
      constant := (990087533151404213148218902148918109613225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree011.table
  base := (1450602634152163828984178307485223628603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3750000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (316478000093266889636289817500000000000)
      linear := (-3452950301438022830677939533187500000000)
      constant := (13770205104054739206749535502705670885809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79052908295447110479/50000000000000000000)
  centralHi := (158105816590894220959/100000000000000000000)
  directionLo := (82911389693848502227/50000000000000000000)
  directionHi := (33164555877539400891/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree012.table
  base := (4551619949759560576146675998079679704687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-606200400424255888329585008581750000000000)
      constant := (2350050649876253598715797396638641244267127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree012.table
  base := (9034098410228239579332448300519107980521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-1215495252404979275135613739823500000000000)
      constant := (4710128331466897580526013201839562065643041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82911389693848502227/50000000000000000000)
  centralHi := (33164555877539400891/20000000000000000000)
  directionLo := (173196244439214613003/100000000000000000000)
  directionHi := (43299061109803653251/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree013.table
  base := (6908298900162230599798777357328331543873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-35464127895714151626020953849534500000000000)
      constant := (136609380658583250623911408676125159153833091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree013.table
  base := (1711361736389430642140538799583301649987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-329209635219822462559786414234625000000000)
      constant := (1268397216458281812101200741398985749648427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173196244439214613003/100000000000000000000)
  centralHi := (43299061109803653251/25000000000000000000)
  directionLo := (180268366642169160657/100000000000000000000)
  directionHi := (90134183321084580329/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree014.table
  base := (250776933332202282051152942685248485043/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-9548358542129621320561079308913625000000000)
      constant := (37163529886782712879414196054901784003177405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree014.table
  base := (309870767725508462976689396667510264203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-531818186007600159503504090270062500000000)
      constant := (2071415520552389622671258204951846826811378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180268366642169160657/100000000000000000000)
  centralHi := (90134183321084580329/50000000000000000000)
  directionLo := (187073325024769031651/100000000000000000000)
  directionHi := (46768331256192257913/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree015.table
  base := (1684497261968427273523182499658610906721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-2273485580073489941025982256765250000000000)
      constant := (9047450842535831266306005365792325759139723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree015.table
  base := (663188299857604635732289499090319234347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-1519525117827911000446209491168500000000000)
      constant := (6053956734450566771619929168403393136779935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187073325024769031651/100000000000000000000)
  centralHi := (46768331256192257913/25000000000000000000)
  directionLo := (193639288006876908797/100000000000000000000)
  directionHi := (96819644003438454399/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree016.table
  base := (1928178454734754253330184248196886564249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-43652046714127152594691044007894500000000000)
      constant := (179077093161587199139618028549411228405401483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree016.table
  base := (1879188022126470738231945706770034388067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-1620868406302221575549741408283500000000000)
      constant := (6659260229738729849539076057708174160956107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193639288006876908797/100000000000000000000)
  centralHi := (96819644003438454399/50000000000000000000)
  directionLo := (24998724587403195307/12500000000000000000)
  directionHi := (199989796699225562457/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree017.table
  base := (662455540102065906838914357279433372111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-46381352986931486250914407394014500000000000)
      constant := (197222969254794697743119267586963408826686637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree017.table
  base := (617153171323218052264256162908574689631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-5166635084329596451959819976195500000000000)
      constant := (22007977340882090290273428062522937612336053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24998724587403195307/12500000000000000000)
  centralHi := (199989796699225562457/100000000000000000000)
  directionLo := (103072381979588644687/50000000000000000000)
  directionHi := (329831622334683663/160000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree018.table
  base := (-56523517228065869344631256635119976199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-227364163239517684755267457315437500000000)
      constant := (1005617083220407424636949041303775482879921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree018.table
  base := (-247054057419128074793473859729042034661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-911777491625421362878402621256750000000000)
      constant := (4040628016824384219782172270609723413806019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103072381979588644687/50000000000000000000)
  centralHi := (329831622334683663/160000000000000000)
  directionLo := (53030303030303030303/25000000000000000000)
  directionHi := (212121212121212121213/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree019.table
  base := (-179385080854621912633397072796124753329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-6479995691567519195420141770781812500000000)
      constant := (29873113815818851657161134238231372930874157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree019.table
  base := (-368470243657204834501940633126738689333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-481224567931288325215084289907125000000000)
      constant := (2223179372018042478501415982797539618590707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53030303030303030303/25000000000000000000)
  centralHi := (212121212121212121213/100000000000000000000)
  directionLo := (108966914193896048363/50000000000000000000)
  directionHi := (217933828387792096727/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree020.table
  base := (-2302080003870776385394912909688099278171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-54569271805344487219584497552374500000000000)
      constant := (262486022766294856823701146972038979658215343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree020.table
  base := (-2337994524543231503350116118166607794797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-6078724680598391627891607230230500000000000)
      constant := (29305384461405105683747552765639271370488689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108966914193896048363/50000000000000000000)
  centralHi := (217933828387792096727/100000000000000000000)
  directionLo := (223595390112915710343/100000000000000000000)
  directionHi := (27949423764114463793/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree021.table
  base := (-306637866374218662785691893342059811517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-1061084779224978164366812239601750000000000)
      constant := (5327287536017693049931408967262303814032215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree021.table
  base := (-619923979745593298316759608623075917627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-2127584848673774451067400993858500000000000)
      constant := (10706894323605641045932560975720164069835665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223595390112915710343/100000000000000000000)
  centralHi := (27949423764114463793/12500000000000000000)
  directionLo := (229117095398257684933/100000000000000000000)
  directionHi := (114558547699128842467/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree022.table
  base := (-467382939041970484365419827929803606477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (378)
      previous := (189)
      next := (189)
      square := (2848302000839402006726608357500000000000)
      linear := (-62012277222059043938048785459312500000000)
      constant := (324908266742094696684561838839520302625121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree022.table
  base := (-753965365951318970453798788116127687559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (112)
      previous := (56)
      next := (56)
      square := (843941333582045039030106180000000000000)
      linear := (-18420893695438719224553164553500000000000)
      constant := (96749393056550291996355468025544361562205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229117095398257684933/100000000000000000000)
  centralHi := (114558547699128842467/50000000000000000000)
  directionLo := (117254411780241408807/50000000000000000000)
  directionHi := (46901764712096563523/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree023.table
  base := (-4329523668821230372760018391938357003201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-62757190623757488188254587710734500000000000)
      constant := (342968374298144099328556850056865887670542333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree023.table
  base := (-4357989692715702504893317185289028660271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-6990814276867186803823394484265500000000000)
      constant := (38300021689381173565611605008949832596321627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117254411780241408807/50000000000000000000)
  centralHi := (46901764712096563523/20000000000000000000)
  directionLo := (59944835709440501229/25000000000000000000)
  directionHi := (239779342837762004917/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree024.table
  base := (-1211439671366415850412709912817772835811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-1819069358237828384568831974912625000000000)
      constant := (10361636352308005056536428272740148460600607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree024.table
  base := (-2436047412513720247062731426273791710161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-1215807357048353088188998372601750000000000)
      constant := (6942959993315489170231109493642621203070519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59944835709440501229/25000000000000000000)
  centralHi := (239779342837762004917/100000000000000000000)
  directionLo := (244936477838023051609/100000000000000000000)
  directionHi := (24493647783802305161/10000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree025.table
  base := (-330913640495024549727836338789476205371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-8526975396170769437587664310371812500000000)
      constant := (50580053429769627492884956745785499974105886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree025.table
  base := (-5318979798439111170386675142291892139487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-2532958002571016751481528662318500000000000)
      constant := (15063587484172923202933093035804556051122073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244936477838023051609/100000000000000000000)
  centralHi := (24493647783802305161/10000000000000000000)
  directionLo := (249987245874031953071/100000000000000000000)
  directionHi := (15624202867126997067/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree026.table
  base := (-1420498152546404821612437040129920941481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-17736277360542622289231169467273625000000000)
      constant := (109453421775882989315344428806832298284181573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree026.table
  base := (-1140904729719967357874989817603607445647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-7902903873135981979755181738300500000000000)
      constant := (48896895077318045949031099248464577486150695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249987245874031953071/100000000000000000000)
  centralHi := (15624202867126997067/6250000000000000000)
  directionLo := (254937968972201263149/100000000000000000000)
  directionHi := (5098759379444025263/2000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree027.table
  base := (-1503241563495282271647012969918730694291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-682170515879396507529148530140875000000000)
      constant := (4375204413679948633647123404344708585990789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree027.table
  base := (-6033800432745482095533514160205865173583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-2735644579519637901688592496548500000000000)
      constant := (17591438650504715046616408362408090313996457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254937968972201263149/100000000000000000000)
  centralHi := (5098759379444025263/2000000000000000000)
  directionLo := (51958873331764383901/20000000000000000000)
  directionHi := (129897183329410959753/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree028.table
  base := (-3145971643910074186903721823896299272829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-38201860993889578234685702320667250000000000)
      constant := (254375603968675897768957274373643790275667657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree028.table
  base := (-6311204571057549211416954880495982497369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-2836987867993948476792124413663500000000000)
      constant := (18940476633527060636922114147445736117818351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51958873331764383901/20000000000000000000)
  centralHi := (129897183329410959753/50000000000000000000)
  directionLo := (16535102088016155113/6250000000000000000)
  directionHi := (264561633408258481809/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree029.table
  base := (-1630687663721852285932824199383516660681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-19783257065145872531398692006863625000000000)
      constant := (136622144564974866785937954445925426069555173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree029.table
  base := (-3270277006273867235003028407978169579377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-4407496734702388577843484496167750000000000)
      constant := (30518425504513955246455213076478861942686149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16535102088016155113/6250000000000000000)
  centralHi := (264561633408258481809/100000000000000000000)
  directionLo := (3365556296783292803/1250000000000000000)
  directionHi := (269244503742663424241/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree030.table
  base := (-1677180909842763144296105812503540350257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-757984579012850220202019735310875000000000)
      constant := (5423363808070692685311541428075821617618903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree030.table
  base := (-6725175702993770159313059429292700909031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3039674444942569626999188247893500000000000)
      constant := (21806457198512338021911011098041208190007249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3365556296783292803/1250000000000000000)
  centralHi := (269244503742663424241/100000000000000000000)
  directionLo := (54769461461519026659/20000000000000000000)
  directionHi := (17115456706724695831/6250000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree031.table
  base := (-1713194272701740499757969513788823194589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-21147910201548039359510373699923625000000000)
      constant := (156611456039781023331316095811163039623277737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree031.table
  base := (-6867976770238323932056728515656163825871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3141017733416880202102720165008500000000000)
      constant := (23322645457567201423765750627398354177069609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54769461461519026659/20000000000000000000)
  centralHi := (17115456706724695831/6250000000000000000)
  directionLo := (34796751968486538597/12500000000000000000)
  directionHi := (278374015747892308777/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree032.table
  base := (-695746502829091239517972187015153081981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-43660473539498245547132429092907250000000000)
      constant := (334323916470990710099825222327019474405840365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree032.table
  base := (-3485752044011363677953340921250315047109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-4863541532836786165809378123185250000000000)
      constant := (37340810412676788875269505333793135637899433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34796751968486538597/12500000000000000000)
  centralHi := (278374015747892308777/100000000000000000000)
  directionLo := (141414141414141414141/50000000000000000000)
  directionHi := (282828282828282828283/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree033.table
  base := (-351251536477863369497923864503198199007/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (84)
      previous := (42)
      next := (42)
      square := (632956000186533779272579635000000000000)
      linear := (-20672693606933155360534486127625000000000)
      constant := (163526627371866075453654003935327027014895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree033.table
  base := (-1759498581014759912185761909255942959223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (28)
      previous := (14)
      next := (14)
      square := (210985333395511259757526545000000000000)
      linear := (-6908479980094011058491289254625000000000)
      constant := (54793121930518909784688583404837807040777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141414141414141414141/50000000000000000000)
  centralHi := (282828282828282828283/100000000000000000000)
  directionLo := (287213478951776376379/100000000000000000000)
  directionHi := (14360673947588818819/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree034.table
  base := (-7057448988506060982337360233727167829481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-92779559624605158406711584958054500000000000)
      constant := (757461840177054295680031144302556342701085573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree034.table
  base := (-3534708078489601359111043460540224218313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-1722523799419905963706657958176750000000000)
      constant := (14100199732606307854884077739996070369584127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287213478951776376379/100000000000000000000)
  centralHi := (14360673947588818819/5000000000000000000)
  directionLo := (58306544200653785553/20000000000000000000)
  directionHi := (145766360501634463883/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree035.table
  base := (-7056461898782331437307121465432471649487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-95508865897409492062934948344174500000000000)
      constant := (804061695557660093199668571387914615121125971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree035.table
  base := (-7067506020727132724021104484288097092921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-10639172661942367507550543500405500000000000)
      constant := (89805746557405106550386079037410920755269677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58306544200653785553/20000000000000000000)
  centralHi := (145766360501634463883/50000000000000000000)
  directionLo := (295788898269622668477/100000000000000000000)
  directionHi := (147894449134811334239/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree036.table
  base := (-7023609264839895501105452924809343626467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3638450821119030582191048582603500000000000)
      constant := (31559871275278348071298910475244069421197493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree036.table
  base := (-1758449619634640528967696585647834735163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-911933543947108269405094937645875000000000)
      constant := (7931058373496722032613368489361674497045277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295788898269622668477/100000000000000000000)
  centralHi := (147894449134811334239/50000000000000000000)
  directionLo := (59996939009767668737/20000000000000000000)
  directionHi := (149992347524419171843/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree037.table
  base := (-6960254538333737025991463223155679439827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-100967478443018159375381675116414500000000000)
      constant := (901621872405063377610906670800471895270085191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree037.table
  base := (-6969652124797778832858860691474199994563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3749077464262743652723911667698500000000000)
      constant := (33567188999847674710112883203267746800657877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59996939009767668737/20000000000000000000)
  centralHi := (149992347524419171843/50000000000000000000)
  directionLo := (9503831576593811143/3125000000000000000)
  directionHi := (304122610451001956577/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree038.table
  base := (-3433803507294733199583989976047675657299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-51848392357911246515802519251267250000000000)
      constant := (476286894353737631561092598776362743627604167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree038.table
  base := (-859533968716824814986147847308640662741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-1443907782276395335435291344305062500000000)
      constant := (13298988596412345336027582849368260314425017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9503831576593811143/3125000000000000000)
  centralHi := (304122610451001956577/100000000000000000000)
  directionLo := (77051243951476552691/25000000000000000000)
  directionHi := (61640995161181242153/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree039.table
  base := (-6746740892482608681607498367890779465561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3941707073652845432882533403283500000000000)
      constant := (37221065330815730151285519299486715684667119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree039.table
  base := (-6754727370333205938307915943087727681173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-3951764041211364802930975501928500000000000)
      constant := (37414445793687540332212601378508634950578067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77051243951476552691/25000000000000000000)
  centralHi := (61640995161181242153/20000000000000000000)
  directionLo := (312233970021691555471/100000000000000000000)
  directionHi := (19514623126355722217/6250000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree040.table
  base := (-1649652923677311299638206190095042863109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-27288849315357790086012941318693625000000000)
      constant := (264700919096515908202227473312954494966222897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree040.table
  base := (-6605970624350022159646440819613388603117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-4053107329685675378034507419043500000000000)
      constant := (39418502461443006068874727487099279979022843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312233970021691555471/100000000000000000000)
  centralHi := (19514623126355722217/6250000000000000000)
  directionLo := (79052908295447110479/25000000000000000000)
  directionHi := (316211633181788441917/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree041.table
  base := (-6424070459064898471030934263422842623637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-111884703534235494000275128660894500000000000)
      constant := (1114075745729114047218592686287437073148577921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree041.table
  base := (-6430848937894328902070427298755443636501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-12463351854479957859414118008475500000000000)
      constant := (124428111165420285054485659601934398959950137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79052908295447110479/25000000000000000000)
  centralHi := (316211633181788441917/100000000000000000000)
  directionLo := (320139878621019779727/100000000000000000000)
  directionHi := (20008742413813736233/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree042.table
  base := (-194496126281568339982907076874835140959/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-1591861247319997606340256833986312500000000)
      constant := (16260867955283140514791027932714114375327532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree042.table
  base := (-3115058903321351896209373356095803636699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2127896953317148264120785626636750000000000)
      constant := (21793479079900970643613287544006095259959421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320139878621019779727/100000000000000000000)
  centralHi := (20008742413813736233/6250000000000000000)
  directionLo := (81005125920936565773/25000000000000000000)
  directionHi := (324020503683746263093/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree043.table
  base := (-1499676452591536523654036877941045840639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-29335829019961040328180463858283625000000000)
      constant := (307230426143168629702874979511396228238632387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree043.table
  base := (-150111286832588483100144209593570164627/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-544642149388575887918137896298562500000000)
      constant := (5718898024007603673047219307627390050400665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81005125920936565773/25000000000000000000)
  centralHi := (324020503683746263093/100000000000000000000)
  directionLo := (327855199335706698321/100000000000000000000)
  directionHi := (163927599667853349161/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree044.table
  base := (-5749164977966438160166759109181896236107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3024)
      previous := (1512)
      next := (1512)
      square := (22786416006715216053812866860000000000000)
      linear := (-992335721922714834454092717514500000000000)
      constant := (10648689288282526269104441459630088801625111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree044.table
  base := (-5754452236930471715900683677980997361867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (336)
      previous := (168)
      next := (168)
      square := (2531824000746135117090318540000000000000)
      linear := (-110540838435940107730131448450500000000000)
      constant := (1189305180340444694060530227220307007914399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327855199335706698321/100000000000000000000)
  centralHi := (163927599667853349161/50000000000000000000)
  directionLo := (82911389693848502227/25000000000000000000)
  directionHi := (331645558775394008909/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree045.table
  base := (-2737897374756889616952452643636853715023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2274109789360237567132751522321750000000000)
      constant := (24990552270183126344959884500036190700482217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree045.table
  base := (-2740329295556588251921045275474096508589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2279911886028614126776083502309250000000000)
      constant := (25119633623544455187796549422965446822460731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82911389693848502227/25000000000000000000)
  centralHi := (331645558775394008909/100000000000000000000)
  directionLo := (67078617033874713103/20000000000000000000)
  directionHi := (83848271292343391379/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree046.table
  base := (-207163178886081887319817961053306271707/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-125531234898257162281391945591494500000000000)
      constant := (1411915378333664902018061349849108210258330775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree046.table
  base := (-2591776178177189690164165391776397294103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2330583530265769414327849460866750000000000)
      constant := (26281500405926461360520297074832368427413537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67078617033874713103/20000000000000000000)
  centralHi := (83848271292343391379/25000000000000000000)
  directionLo := (169549599309035539349/50000000000000000000)
  directionHi := (339099198618071078699/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree047.table
  base := (-971890582618626736499656543734725342161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-128260541171061495937615308977614500000000000)
      constant := (1475766653996032666629899508711009761535800065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree047.table
  base := (-2431782472894634396009258624043533198237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-7143765523508774105638846258272750000000000)
      constant := (82409686150550922842107178627309822449039969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169549599309035539349/50000000000000000000)
  centralHi := (339099198618071078699/100000000000000000000)
  directionLo := (42845655305447352397/12500000000000000000)
  directionHi := (342765242443578819177/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree048.table
  base := (-4517303787996287691441676710255469365833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-4851475831254289984956987865323500000000000)
      constant := (57075643690479012967192699272867088206734207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree048.table
  base := (-904216576356625840709664690956456500301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-4863853637480159978862762755963500000000000)
      constant := (57369590343425788476464757156818343817317895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42845655305447352397/12500000000000000000)
  centralHi := (342765242443578819177/100000000000000000000)
  directionLo := (346392488878429226007/100000000000000000000)
  directionHi := (43299061109803653251/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree049.table
  base := (-4152980638853660856930946021462636398027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-133719153716670163250062035749854500000000000)
      constant := (1607741416587678593039878400646717066887645791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree049.table
  base := (-2078226331509826460568775810143097541787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2482598462977235276983147336539250000000000)
      constant := (29926178807343857848583956148642872697443773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346392488878429226007/100000000000000000000)
  centralHi := (43299061109803653251/12500000000000000000)
  directionLo := (349982144223644734299/100000000000000000000)
  directionHi := (3499821442236447343/1000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree050.table
  base := (-235424759138410462245489218638712747411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-17056057498684312113285674891996812500000000)
      constant := (209482842912864223232514009409161525908416526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree050.table
  base := (-471248133348833089774350312981137879589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-1899952580410792923401184971322562500000000)
      constant := (23395520616287782284724428930402300074709193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349982144223644734299/100000000000000000000)
  centralHi := (3499821442236447343/1000000000000000000)
  directionLo := (353535353535353535353/100000000000000000000)
  directionHi := (176767676767676767677/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree051.table
  base := (-1679515474068140100532458215839421274923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-7732098125682157253472709029005250000000000)
      constant := (96966969052450323224148511968385540077202951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree051.table
  base := (-3361958958771053889140936556938443620289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-5167883502903091704173358507308500000000000)
      constant := (64976648686918238058131527593551948321945031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353535353535353535353/100000000000000000000)
  centralHi := (176767676767676767677/50000000000000000000)
  directionLo := (22315825305724288407/6250000000000000000)
  directionHi := (357053204891588614513/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree052.table
  base := (-2929937027837819352289698705536726978433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-141907072535083164218732125908214500000000000)
      constant := (1816368692282078150962373384737625512961459389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree052.table
  base := (-117304986886685171089446377019862816611/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-5269226791377402279276890424423500000000000)
      constant := (67618108454822208223732578751564164979751725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22315825305724288407/6250000000000000000)
  centralHi := (357053204891588614513/100000000000000000000)
  directionLo := (72107346656867664263/20000000000000000000)
  directionHi := (90134183321084580329/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree053.table
  base := (-49594814465902410064015116086958116811/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-72318189403943748937477744647167250000000000)
      constant := (944375875935331701431453008741654445809461575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree053.table
  base := (-1241103504701156388550913919459119482877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-8055855119777569281570633512307750000000000)
      constant := (105468610619079143810228669686279027127715649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72107346656867664263/20000000000000000000)
  centralHi := (90134183321084580329/25000000000000000000)
  directionLo := (90996731044077022993/25000000000000000000)
  directionHi := (363986924176308091973/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree054.table
  base := (-2008645404658278645590052011342278051461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-5457988336321919686339957506683500000000000)
      constant := (72687183603688193088818028383506584355773219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree054.table
  base := (-502726978039553365863081720671397569351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-1367978342081505857370988564663375000000000)
      constant := (18264880031416606577337672529018542144108529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90996731044077022993/25000000000000000000)
  centralHi := (363986924176308091973/100000000000000000000)
  directionLo := (183702358378517288707/50000000000000000000)
  directionHi := (73480943351406915483/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree055.table
  base := (-1516833859155543323073344068057001122567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3024)
      previous := (1512)
      next := (1512)
      square := (22786416006715216053812866860000000000000)
      linear := (-1240454473995836075928943934434500000000000)
      constant := (16841113317379809019082007884934960969690691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree055.table
  base := (-303781767876622767306729001056360548779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (112)
      previous := (56)
      next := (56)
      square := (843941333582045039030106180000000000000)
      linear := (-46059972370250694252789141948500000000000)
      constant := (626937401959755845857830951445968197256105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183702358378517288707/50000000000000000000)
  centralHi := (73480943351406915483/20000000000000000000)
  directionLo := (370791006928841456007/100000000000000000000)
  directionHi := (46348875866105182001/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree056.table
  base := (-251117604469884090623114070570892648863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-38206074406575124710906394863173625000000000)
      constant := (528603369327777710271780585159277893716164579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree056.table
  base := (-1006372887619072300296981863514080761593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-17023799835823933739073054278650500000000000)
      constant := (236136311637289799774844748977128888683541741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370791006928841456007/100000000000000000000)
  centralHi := (46348875866105182001/12500000000000000000)
  directionLo := (374146650049538063303/100000000000000000000)
  directionHi := (46768331256192257913/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree057.table
  base := (-471702854369412609174939931772575698679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-5761244588855734537031442327363500000000000)
      constant := (81202584157329283105666659852230018340459841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree057.table
  base := (-236723341762017960287655063411759232041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-2887971616874477577397275004999250000000000)
      constant := (40808768554869621221418507012657114632923039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374146650049538063303/100000000000000000000)
  centralHi := (46768331256192257913/12500000000000000000)
  directionLo := (377472463455652416543/100000000000000000000)
  directionHi := (11796014482989138017/3125000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree058.table
  base := (81335918922199654294694949092198912697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-158282910171909166156072306224934500000000000)
      constant := (2271943161988313563007351785914095213847781099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree058.table
  base := (79737925353828802272043363456357491367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-5877286522223265729898081927113500000000000)
      constant := (84575709375505056755920359675974594256455407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377472463455652416543/100000000000000000000)
  centralHi := (11796014482989138017/3125000000000000000)
  directionLo := (15230769151491526553/4000000000000000000)
  directionHi := (190384614393644081913/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree059.table
  base := (163631583365974254638635441246494169431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-40253054111178374953073917402763625000000000)
      constant := (588208313975496875902948225375459921451531077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree059.table
  base := (326531179381497724205102379982649427547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-8967944716046364457502420766342750000000000)
      constant := (131379909492275412251097400313240201742199561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15230769151491526553/4000000000000000000)
  centralHi := (190384614393644081913/50000000000000000000)
  directionLo := (76807538826668191987/20000000000000000000)
  directionHi := (6000588970833452499/1562500000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree060.table
  base := (1247760806782146850015183882162368951791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-18193502524168648163168781444130500000000000)
      constant := (270571078057441270505820726514554939929500133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree060.table
  base := (311604987730044023197362873763965589387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-1519993274792971720026286440335875000000000)
      constant := (22662553765303779709584929798296377336315827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76807538826668191987/20000000000000000000)
  centralHi := (6000588970833452499/1562500000000000000)
  directionLo := (77455715202750763519/20000000000000000000)
  directionHi := (96819644003438454399/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree061.table
  base := (1860942526325538965157917000046980197469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-166470828990322167124742396383294500000000000)
      constant := (2518862185546659898759577090351582984305131223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree061.table
  base := (1859714739112543617158301384922707480213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-6181316387646197455208677678458500000000000)
      constant := (93766523963111336687436287284810272605105773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77455715202750763519/20000000000000000000)
  centralHi := (96819644003438454399/25000000000000000000)
  directionLo := (12202892537927844921/3125000000000000000)
  directionHi := (390492561213691037473/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree062.table
  base := (15587402247370926024786107817606254837/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-21150016907890812597620719971176812500000000)
      constant := (325500052541140911125613641963428517691049580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree062.table
  base := (2492860378271101099633571960511740361827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-18847979028361524090936628786720500000000000)
      constant := (290806567758356739261420318214836636751343201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12202892537927844921/3125000000000000000)
  centralHi := (390492561213691037473/100000000000000000000)
  directionLo := (196840154241465421489/50000000000000000000)
  directionHi := (393680308482930842979/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree063.table
  base := (314680787677182135517181234660993726527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-3183878546961682119207205984361750000000000)
      constant := (49825076863598320147022472992112651204548835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree063.table
  base := (393222395984063866123753098813664065017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-798000370574352325676967689086062500000000)
      constant := (12519650191059315523311615212925297101867057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196840154241465421489/50000000000000000000)
  centralHi := (393680308482930842979/100000000000000000000)
  directionLo := (396842450112387722713/100000000000000000000)
  directionHi := (198421225056193861357/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree064.table
  base := (1909671237047766846074813873771301936897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-87329373904367584046706243270827250000000000)
      constant := (1389261572899783519294280938494874843427842499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree064.table
  base := (95460029477677498731578556833232253173/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-810668281633641147564909178725437500000000)
      constant := (12928944041099024941702878443798605513169665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396842450112387722713/100000000000000000000)
  centralHi := (198421225056193861357/50000000000000000000)
  directionLo := (399979593398451124913/100000000000000000000)
  directionHi := (199989796699225562457/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree065.table
  base := (4511524586746983843390096971711876118239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-177388054081539501749635849927774500000000000)
      constant := (2867907198158687502102913825738050199278286813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree065.table
  base := (4510663471629366108711504503379164269437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-19760068624630319266868416040755500000000000)
      constant := (320275702113870400140809135411984761629805631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399979593398451124913/100000000000000000000)
  centralHi := (199989796699225562457/50000000000000000000)
  directionLo := (403092322004745750199/100000000000000000000)
  directionHi := (2015461610023728751/500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree066.table
  base := (2611648491147167871212077034384547345293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (56)
      previous := (28)
      next := (28)
      square := (421970666791022519515053090000000000000)
      linear := (-27566170853128839211181391691750000000000)
      constant := (452816975931024773500629774924884547345293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree066.table
  base := (522250939041307563040895699289122740759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (56)
      previous := (28)
      next := (28)
      square := (421970666791022519515053090000000000000)
      linear := (-27636499297594009631100567206750000000000)
      constant := (455116693391364262146383924674383113703795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403092322004745750199/100000000000000000000)
  centralHi := (2015461610023728751/500000000000000000)
  directionLo := (406181197229961622413/100000000000000000000)
  directionHi := (203090598614980811207/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree067.table
  base := (1488652031485305801434839629588686539059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-45711666656787042265520644175003625000000000)
      constant := (762729936289818103529407526168292863923105753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree067.table
  base := (5953887934290262587175228488303114597763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-6789376118492060905829869181148500000000000)
      constant := (113570563445910929833899808630325176866329323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406181197229961622413/100000000000000000000)
  centralHi := (203090598614980811207/50000000000000000000)
  directionLo := (51155844898694178229/12500000000000000000)
  directionHi := (409246759189553425833/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree068.table
  base := (670541161018433287820843447309376049383/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-92787986449976251359152970043067250000000000)
      constant := (1572273959911621904782629240743301657766671305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree068.table
  base := (1676188297170649592269413813332976322163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-5168039555224778610700050823697625000000000)
      constant := (87791649563421368101419417051958557904945169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51155844898694178229/12500000000000000000)
  centralHi := (409246759189553425833/100000000000000000000)
  directionLo := (103072381979588644687/25000000000000000000)
  directionHi := (412289527918354578749/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree069.table
  base := (1868916410545352436016967255315108290239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-5230702199243245454848036207562625000000000)
      constant := (89988625227444844701652796753246759309356757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree069.table
  base := (7475063815851990758110521167714249114669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-6992062695440682056036933015378500000000000)
      constant := (120593142714796525185024460437507549142874949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103072381979588644687/25000000000000000000)
  centralHi := (412289527918354578749/100000000000000000000)
  directionLo := (207655002200240187143/50000000000000000000)
  directionHi := (415310004400480374287/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree070.table
  base := (413266629143454544783116094995059244123/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-47758646361390292507688166714593625000000000)
      constant := (834011846821691051645261678231235542752749205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree070.table
  base := (8264782596719575887773525205537846501387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7093405983914992631140464932493500000000000)
      constant := (124183388833106490455448985310878204426667827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207655002200240187143/50000000000000000000)
  centralHi := (415310004400480374287/100000000000000000000)
  directionLo := (418308671532296083817/100000000000000000000)
  directionHi := (209154335766148041909/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree071.table
  base := (9074378532509076840394106935909575656331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-193763891718365503686976030244494500000000000)
      constant := (3433918446369048177087579930183241083669233377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree071.table
  base := (283558625591905273068586417187014524591/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-2698030977145988702341498818603187500000000)
      constant := (47934850144186768509660611454508138839706132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418308671532296083817/100000000000000000000)
  centralHi := (209154335766148041909/50000000000000000000)
  directionLo := (3291296836122588963/781250000000000000)
  directionHi := (84257199004738277453/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree072.table
  base := (4951386478953637277956277631888519236299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-3638762925762404395244433215381750000000000)
      constant := (65429696031165207756945938883484510827592179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree072.table
  base := (2475578476622850342369062997391732674531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-1824023140215903445336882191680875000000000)
      constant := (32880443429418051243808684849487024653618251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3291296836122588963/781250000000000000)
  centralHi := (84257199004738277453/20000000000000000000)
  directionLo := (53030303030303030303/12500000000000000000)
  directionHi := (16969696969696969697/4000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree073.table
  base := (2687622089263210025201497808338860402459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-49805626065993542749855689254183625000000000)
      constant := (908475678844828476196739269287668931934833553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree073.table
  base := (10750069086516337497321842575549912932951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7397435849337924356451060683838500000000000)
      constant := (135269905544713558413468478620260414464887071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53030303030303030303/12500000000000000000)
  centralHi := (16969696969696969697/4000000000000000000)
  directionLo := (106794598251467177371/25000000000000000000)
  directionHi := (85435678601173741897/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree074.table
  base := (2904374989342592982583686322316428177089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-50487952634194626163911530100713625000000000)
      constant := (934003938631555599494136140518338520854549763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree074.table
  base := (11617117089649159047061779339044594491157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-22496337413436704794663777802860500000000000)
      constant := (417211978714486246660283422566769312800289991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106794598251467177371/25000000000000000000)
  centralHi := (85435678601173741897/20000000000000000000)
  directionLo := (215047160162058271833/50000000000000000000)
  directionHi := (430094320324116543667/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree075.table
  base := (12503785444175636691186612946021867756501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7580782104058623641180351251443500000000000)
      constant := (142205282600799011410317488237856145998536621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree075.table
  base := (12503435880394345893453918915508038842191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7600122426286545506658124518068500000000000)
      constant := (142924033131722818459958426756826472699905111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215047160162058271833/50000000000000000000)
  centralHi := (430094320324116543667/100000000000000000000)
  directionLo := (432990611098036532509/100000000000000000000)
  directionHi := (43299061109803653251/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree076.table
  base := (13409324716279008890701058793489759636869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-207410423082387171968092847175094500000000000)
      constant := (3944483276794780128608517969012053044733651023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree076.table
  base := (13409005614528071280666436910586556273263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7701465714760856081761656435183500000000000)
      constant := (146830023824244684095604685572253723309064823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432990611098036532509/100000000000000000000)
  centralHi := (43299061109803653251/10000000000000000000)
  directionLo := (108966914193896048363/25000000000000000000)
  directionHi := (435867656775584193453/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree077.table
  base := (143340996659963594930565889404925523853/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (756)
      previous := (378)
      next := (378)
      square := (5696604001678804013453216715000000000000)
      linear := (-434172994535519639719661592068625000000000)
      constant := (8369499246049666962823043597728699728600775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree077.table
  base := (7166904210391697266827557877121176265679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (168)
      previous := (84)
      next := (84)
      square := (1265912000373067558545159270000000000000)
      linear := (-96729037230188016407419690317750000000000)
      constant := (1869280530826087346760573144329301028797037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108966914193896048363/25000000000000000000)
  centralHi := (435867656775584193453/100000000000000000000)
  directionLo := (87745167193874743609/20000000000000000000)
  directionHi := (219362917984686859023/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree078.table
  base := (7639046990554430160919451698371453522029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-11826057534888657737807754108185250000000000)
      constant := (231033647322740580034429558956653337628496527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree078.table
  base := (15277828204368672052733775615062874186007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-7904152291709477231968720269413500000000000)
      constant := (154799848171432115213641043208155232776506847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87745167193874743609/20000000000000000000)
  centralHi := (219362917984686859023/50000000000000000000)
  directionLo := (441565515038270580211/100000000000000000000)
  directionHi := (110391378759567645053/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree079.table
  base := (16241292966564940987687202374873753559611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-215598341900800172936762937333454500000000000)
      constant := (4267787278949921539986613115863933052879249137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree079.table
  base := (8120525235059643139313092143706614574777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-4002747790091893903536126093264250000000000)
      constant := (79431839062356486547898345086073375363548017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441565515038270580211/100000000000000000000)
  centralHi := (110391378759567645053/25000000000000000000)
  directionLo := (88877409727106811121/20000000000000000000)
  directionHi := (222193524317767027803/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree080.table
  base := (17223683383942819335838863552484975898531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-218327648173604506592986300719574500000000000)
      constant := (4378382473259888145807386778105928416260500777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree080.table
  base := (27557539461292298584314909882269014347/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-24320516605974295146527352310930500000000000)
      constant := (488940353300574757989062328720174782629975625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88877409727106811121/20000000000000000000)
  centralHi := (222193524317767027803/50000000000000000000)
  directionLo := (223595390112915710343/50000000000000000000)
  directionHi := (447190780225831420687/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree081.table
  base := (18225253306893586043519146468074299376109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-8187294609126253342563320892803500000000000)
      constant := (166310785028735124863872147068815490224509189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree081.table
  base := (9112525763169003722456732943413639251923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-4104091078566204478639658010379250000000000)
      constant := (83574582837599427087795951825782237849482683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223595390112915710343/50000000000000000000)
  centralHi := (447190780225831420687/100000000000000000000)
  directionLo := (449977042573257515527/100000000000000000000)
  directionHi := (56247130321657189441/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree082.table
  base := (19245991990965361631831383503230954352127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-223786260719213173905433027491814500000000000)
      constant := (4603813411395677926280541281010854527868398909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree082.table
  base := (9622903984865889814856266281898393855511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-4154762722803359766191423968936750000000000)
      constant := (85685410284203941433902188805364643156516831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449977042573257515527/100000000000000000000)
  centralHi := (56247130321657189441/12500000000000000000)
  directionLo := (226373079101161317199/50000000000000000000)
  directionHi := (452746158202322634399/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree083.table
  base := (2535736219546356565121734588598649591637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-28314445874002188445207048859741812500000000)
      constant := (589831136061938965318769320170564100715878079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree083.table
  base := (10142860977986388393840988474536868793801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-12616303101121545161229569782482750000000000)
      constant := (263467621938668813021170261597206133372149763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226373079101161317199/50000000000000000000)
  centralHi := (452746158202322634399/100000000000000000000)
  directionLo := (455498439833716557891/100000000000000000000)
  directionHi := (113874609958429139473/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree084.table
  base := (21344937882405735698180438114704981723159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-8490550861660068193254805713483500000000000)
      constant := (179070303651289212475951136141513302788502239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree084.table
  base := (10672392447461930454562558948208360742321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-4256106011277670341294955886051750000000000)
      constant := (89985973403953118957672997797546836649820841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455498439833716557891/100000000000000000000)
  centralHi := (113874609958429139473/25000000000000000000)
  directionLo := (229117095398257684933/50000000000000000000)
  directionHi := (458234190796515369867/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree085.table
  base := (5605782128088872241524735276207692626013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-57993544884406543718525779412543625000000000)
      constant := (1238140178998920656290842556681234906809184471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree085.table
  base := (350359203900915692404638556897854357033/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1076694413878706407211680461152312500000000)
      constant := (23043927022327609102775535697763763642607944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229117095398257684933/50000000000000000000)
  centralHi := (458234190796515369867/100000000000000000000)
  directionLo := (460953705418369101031/100000000000000000000)
  directionHi := (57619213177296137629/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree086.table
  base := (23520454567845141328634732895055415524307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-234703485810430508530326481036294500000000000)
      constant := (5071636617603082357243981983431063042517910969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree086.table
  base := (5880081862916763292080951905767642456193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-6536173949627971374597731704750125000000000)
      constant := (141587616421050056740610420534966497961598059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460953705418369101031/100000000000000000000)
  centralHi := (57619213177296137629/12500000000000000000)
  directionLo := (28978579337193184701/6250000000000000000)
  directionHi := (463657269395090955217/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree087.table
  base := (6159227417922838246143824116822437041773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-6595355335645412282959717900622625000000000)
      constant := (144225718960354165610054295912253669646163599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree087.table
  base := (4927358764899933944908137751708587827233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-8816241887978272407900507523448500000000000)
      constant := (193268163196793452343683125849622945635475965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28978579337193184701/6250000000000000000)
  centralHi := (463657269395090955217/100000000000000000000)
  directionLo := (466345160140961788871/100000000000000000000)
  directionHi := (58293145017620223609/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree088.table
  base := (25772488078410497131067524619923260402237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3024)
      previous := (1512)
      next := (1512)
      square := (22786416006715216053812866860000000000000)
      linear := (-1984810730215199800353497585194500000000000)
      constant := (43917590844084218434317083749813928030860399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree088.table
  base := (25772382515007497344443803412458300333521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (112)
      previous := (56)
      next := (56)
      square := (843941333582045039030106180000000000000)
      linear := (-73699051045062669281025119343500000000000)
      constant := (1634755697527024620971912664191958300333521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466345160140961788871/100000000000000000000)
  centralHi := (58293145017620223609/12500000000000000000)
  directionLo := (117254411780241408807/25000000000000000000)
  directionHi := (469017647120965635229/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree089.table
  base := (26927184611621119125214128788137736157619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-242891404628843509498996571194654500000000000)
      constant := (5437344429376165550696873984348861484026941273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree089.table
  base := (5385417686284209531013893454231560592829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-27056785394780680674322714073035500000000000)
      constant := (607185949671676643828320623392443907475984635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117254411780241408807/25000000000000000000)
  centralHi := (469017647120965635229/100000000000000000000)
  directionLo := (471674992166082504987/100000000000000000000)
  directionHi := (117918748041520626247/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree090.table
  base := (7025248651913820998829527209816333319253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-2274265841681924473659443838710875000000000)
      constant := (51500682213541409063360565789554026331629613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree090.table
  base := (28100906987586304865086809738967343928593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-9120271753401204133211103274793500000000000)
      constant := (207037794111235522848448416798309423615359753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471674992166082504987/100000000000000000000)
  centralHi := (117918748041520626247/25000000000000000000)
  directionLo := (237158724886341331437/50000000000000000000)
  directionHi := (3794539598181461303/800000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree091.table
  base := (14646956932380887610391250893107609788463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-124175008587226088405721648983447250000000000)
      constant := (2844108113732994545308889109208789811178908621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree091.table
  base := (5858766810548892633151056320868464460987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-9221615041875514708314635191908500000000000)
      constant := (211732871562978088351768452915114420998897135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237158724886341331437/50000000000000000000)
  centralHi := (3794539598181461303/800000000000000000)
  directionLo := (476945267386991364943/100000000000000000000)
  directionHi := (29809079211686960309/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree092.table
  base := (3813242324668208222014768455865303046711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4083750000000000000000000000000000000000000
      center := (45738)
      previous := (22869)
      next := (22869)
      square := (344644542101567642813919611257500000000000)
      linear := (-31384915430907063808458332669126812500000000)
      constant := (726971507777397207428639029765586195053604837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree092.table
  base := (30505865906303349231896840367785252897683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-27968874991049475850254501327070500000000000)
      constant := (649441645386784774441161319016371296801858929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476945267386991364943/100000000000000000000)
  centralHi := (29809079211686960309/6250000000000000000)
  directionLo := (59944835709440501229/12500000000000000000)
  directionHi := (479558685675524009833/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree093.table
  base := (15868532697372076199888662768997910816343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-4700159809630756372664630087761750000000000)
      constant := (110087799484803750130027162227168997208777503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree093.table
  base := (6347399839420727818997847632116297184391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-9424301618824135858521699026138500000000000)
      constant := (221280824403595754034113185077222984796556555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59944835709440501229/12500000000000000000)
  centralHi := (479558685675524009833/100000000000000000000)
  directionLo := (60269742347791029829/12500000000000000000)
  directionHi := (482157938782328238633/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree094.table
  base := (8246822796022089291224846163506255677259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-64134483998216294445028347031313625000000000)
      constant := (1518780886826900252301947009665903187297605153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree094.table
  base := (32987230906732588479658831669722742049653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-9525644907298446433625230943253500000000000)
      constant := (226133699021752633955626478289538076788008013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60269742347791029829/12500000000000000000)
  centralHi := (482157938782328238633/100000000000000000000)
  directionLo := (484743254573811200753/100000000000000000000)
  directionHi := (242371627286905600377/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree095.table
  base := (17128306598422810883876857927839467878959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-129633621132834755718168375755687250000000000)
      constant := (3103459589279488485654894086627977791560559053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree095.table
  base := (34256558316482623201957907156862684809381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-28880964587318271026186288581105500000000000)
      constant := (693117515963305844306007937840187404585805303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484743254573811200753/100000000000000000000)
  centralHi := (242371627286905600377/50000000000000000000)
  directionLo := (487314854871876527149/100000000000000000000)
  directionHi := (9746297097437530543/2000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree096.table
  base := (7109005787735431135228581868572154353401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-29110727615385982788062234988610500000000000)
      constant := (704458673087169507184308691803026460151422815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree096.table
  base := (7108995795518457513830498179189808323963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-9728331484247067583832294777483500000000000)
      constant := (235997243005343560334420877227943834035997615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487314854871876527149/100000000000000000000)
  centralHi := (9746297097437530543/2000000000000000000)
  directionLo := (489872955676046103219/100000000000000000000)
  directionHi := (24493647783802305161/5000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree097.table
  base := (36852536162282203072929270484580348640031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-264725854811278178748783478283614500000000000)
      constant := (6474750177642315220000169349218015499006981277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree097.table
  base := (2303280667777698593210757012587526499581/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1228709346590172269866978336824812500000000)
      constant := (30125988975949705469750855647528353287898602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489872955676046103219/100000000000000000000)
  centralHi := (24493647783802305161/5000000000000000000)
  directionLo := (123104441843799034557/25000000000000000000)
  directionHi := (492417767375196138229/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree098.table
  base := (38179132842932572248179701213815451161301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-267455161084082512405006841669734500000000000)
      constant := (6610785531517558935017610110843326078943970367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree098.table
  base := (38179091450418997935001867716175702174033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-29793054183587066202118075835140500000000000)
      constant := (738213534462450880021079439492128404889173979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123104441843799034557/25000000000000000000)
  centralHi := (492417767375196138229/100000000000000000000)
  directionLo := (247474747474747474747/50000000000000000000)
  directionHi := (98989898989898989899/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree099.table
  base := (9881204289107697447345978111462472164469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (28)
      previous := (14)
      next := (14)
      square := (210985333395511259757526545000000000000)
      linear := (-20675272984151120757669896315875000000000)
      constant := (516393795029890079895349663044337472164469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree099.table
  base := (39524779486162146281447556956136170361687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (112)
      previous := (56)
      next := (56)
      square := (843941333582045039030106180000000000000)
      linear := (-82912077269999994290437111808500000000000)
      constant := (2075925965524704455906032090254636170361687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247474747474747474747/50000000000000000000)
  centralHi := (98989898989898989899/20000000000000000000)
  directionLo := (497468338163091013363/100000000000000000000)
  directionHi := (124367084540772753341/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree100.table
  base := (40889587459251628279909476678150844376321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-272913773629691179717453568441974500000000000)
      constant := (6887095918072052189194489066027468808577440707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree100.table
  base := (40889553179989561563452498803341960565697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-10133704638144309884246422445943500000000000)
      constant := (256355502635600830853778996035260627228449337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497468338163091013363/100000000000000000000)
  centralHi := (124367084540772753341/25000000000000000000)
  directionLo := (249987245874031953071/50000000000000000000)
  directionHi := (499974491748063906143/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree101.table
  base := (42273442270650604505360799955603954946133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-275643079902495513373676931828094500000000000)
      constant := (7027370940544312583722358713484167620809016511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree101.table
  base := (42273411080253288439575231755473446609841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-30705143779855861378049863089175500000000000)
      constant := (784729681199506997434478206996833236119372283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249987245874031953071/50000000000000000000)
  centralHi := (499974491748063906143/100000000000000000000)
  directionLo := (502468145580117517569/100000000000000000000)
  directionHi := (50246814558011751757/10000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree102.table
  base := (2729773766034032483150459619356272552069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1288761047107869662175464329695437500000000)
      constant := (33190088780133958043461636587285092957600698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree102.table
  base := (8735270375890509639119950709235081388491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-10336391215092931034453486280173500000000000)
      constant := (266850214962986149813350965537633349240037055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502468145580117517569/100000000000000000000)
  centralHi := (50246814558011751757/10000000000000000000)
  directionLo := (63118685605808017659/12500000000000000000)
  directionHi := (504949484846464141273/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree103.table
  base := (45098400214988451988271604513203709796831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-281101692448104180686123658600334500000000000)
      constant := (7312160622039165190125091230468725019906246877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree103.table
  base := (22549187199961662134160457541315557934453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-5218867251783620804778509098644250000000000)
      constant := (136088233091277468427602931305548307510068813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63118685605808017659/12500000000000000000)
  centralHi := (504949484846464141273/100000000000000000000)
  directionLo := (507418690206319526409/100000000000000000000)
  directionHi := (50741869020631952641/10000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree104.table
  base := (23269750531545513021009498700416334225193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-141915499360454257171173510993227250000000000)
      constant := (3728337636798598609517713353609114163913705531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree104.table
  base := (23269738790474384986955285270875068236879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (20328)
      previous := (10164)
      next := (10164)
      square := (153175352045141174583964271670000000000000)
      linear := (-15808616688062328276990825171605250000000000)
      constant := (416332970895292932732471331862110399769987077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507418690206319526409/100000000000000000000)
  centralHi := (50741869020631952641/10000000000000000000)
  directionLo := (509875937944402526299/100000000000000000000)
  directionHi := (5098759379444025263/1000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree105.table
  base := (47999681825225471707584184171948799386913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-31840033888190316444285598374730500000000000)
      constant := (844733680888406485103042048875244914177449419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree105.table
  base := (2999978779196832683605130240889311565887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1330052635064482844970510253939812500000000)
      constant := (35373344761288284708167369808022322773944654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509875937944402526299/100000000000000000000)
  centralHi := (5098759379444025263/1000000000000000000)
  directionLo := (64040175014726054303/12500000000000000000)
  directionHi := (20492856004712337377/4000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree106.table
  base := (49478941622408108218884640987483052021847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-289289611266517181654793748758694500000000000)
      constant := (7749944182362908945738154823063414130955374149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree106.table
  base := (24739461099012718237974599402474338768997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-5370882184495086667433806974316750000000000)
      constant := (144235399279383729618777018638691082491048637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64040175014726054303/12500000000000000000)
  centralHi := (20492856004712337377/4000000000000000000)
  directionLo := (128688811174150575499/25000000000000000000)
  directionHi := (514755244696602301997/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree107.table
  base := (50977279662728616558752110293111360496583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-292018917539321515311017112144814500000000000)
      constant := (7898698434111777946238667159346881314742336661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree107.table
  base := (50977261998538467830748556550568198543513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-32529322972393451729913437597245500000000000)
      constant := (882022305725397472293737673782920256071295219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128688811174150575499/25000000000000000000)
  centralHi := (514755244696602301997/100000000000000000000)
  directionLo := (103435527139691468889/20000000000000000000)
  directionHi := (258588817849228672223/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree108.table
  base := (52494695232727922886276594532545045384873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-10916600881930586998786684278923500000000000)
      constant := (298106143737459058266320832841155950491569633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree108.table
  base := (6561834896328329509948918153924520754081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1368056368242349310634334722857937500000000)
      constant := (37449583506866987094349171772491210761243801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103435527139691468889/20000000000000000000)
  centralHi := (258588817849228672223/50000000000000000000)
  directionLo := (519588733317643839011/100000000000000000000)
  directionHi := (129897183329410959753/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree109.table
  base := (2161247507585193602935782548637762507567/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-297477530084930182623463838917054500000000000)
      constant := (8200446520661809023246757252679594752805534725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree109.table
  base := (54031173085563204115217956363486171992181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-11045794234413105060178209699978500000000000)
      constant := (305238496922101742018218073407693451811053901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519588733317643839011/100000000000000000000)
  centralHi := (129897183329410959753/25000000000000000000)
  directionLo := (260994347024327787951/50000000000000000000)
  directionHi := (521988694048655575903/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree110.table
  base := (55586756454341914053532906726340992516373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (3024)
      previous := (1512)
      next := (1512)
      square := (22786416006715216053812866860000000000000)
      linear := (-2481048234361442283303200019034500000000000)
      constant := (69036697119596084702243447134156206797942071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree110.table
  base := (11117348635414652424174357636736575985519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (336)
      previous := (168)
      next := (168)
      square := (2531824000746135117090318540000000000000)
      linear := (-276375310484811957899547312820500000000000)
      constant := (7709080705159770970256837358617923639782785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260994347024327787951/50000000000000000000)
  centralHi := (521988694048655575903/100000000000000000000)
  directionLo := (262188835402371922429/50000000000000000000)
  directionHi := (524377670804743844859/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree111.table
  base := (57161401005149299007724544225187320108969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-11219857134464401849478169099603500000000000)
      constant := (315105458208700142558303577413781165733185249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree111.table
  base := (57161388935133795961235065654576706957381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-11248480811361726210385273534208500000000000)
      constant := (316679942551250173390843023570091531541843101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262188835402371922429/50000000000000000000)
  centralHi := (524377670804743844859/100000000000000000000)
  directionLo := (26337790651580651019/5000000000000000000)
  directionHi := (526755813031613020381/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree112.table
  base := (58755120872033032027040768747467785824197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-305665448903343183592133929075414500000000000)
      constant := (8663667579617589871731505626208961256287651599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree112.table
  base := (117510219800778408432983295736478156703/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-2837456024959009196372201362830875000000000)
      constant := (80619889798984486754468017668834982120132875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26337790651580651019/5000000000000000000)
  centralHi := (526755813031613020381/100000000000000000000)
  directionLo := (529123266816516963617/100000000000000000000)
  directionHi := (264561633408258481809/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree113.table
  base := (3018395781577543815479263416140066048407/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-77098688794036879312089323115383625000000000)
      constant := (2205225243508949632327897240034068853900728345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree113.table
  base := (60367905659121164422617397025324253326021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-34353502164931042081777012105315500000000000)
      constant := (984995314976342498989897982318841828957345623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529123266816516963617/100000000000000000000)
  centralHi := (264561633408258481809/50000000000000000000)
  directionLo := (16608755468530675173/3125000000000000000)
  directionHi := (531480174992981605537/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree114.table
  base := (61999784902225026466644440951230363916861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-34569340160994650100508961760850500000000000)
      constant := (997727505960360203512168806024463622101820543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree114.table
  base := (15499943959679454111828276205019812585423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-2888127669196164483923967321388375000000000)
      constant := (83559144973673199062779147414479366072836183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16608755468530675173/3125000000000000000)
  centralHi := (531480174992981605537/100000000000000000000)
  directionLo := (33364167327585383763/6250000000000000000)
  directionHi := (533826677241366140209/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree115.table
  base := (63650728340386487017891294263099542025157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-313853367721756184560804019233774500000000000)
      constant := (9139607317317153170391068224388988703796187919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree115.table
  base := (1989085003237271732590993954467272987253/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1456731745657371063849925150333562500000000)
      constant := (42524247982883484316844519325049347625830452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33364167327585383763/6250000000000000000)
  centralHi := (533826677241366140209/100000000000000000000)
  directionLo := (536162910185463170503/100000000000000000000)
  directionHi := (67020363773182896313/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree116.table
  base := (2612829825457236235365434249831873363311/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-316582673994560518217027382619894500000000000)
      constant := (9301080264046055127413522232077520256948425925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree116.table
  base := (816509226893859605554054706592326302967/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-4408198970149979657213599919918812500000000)
      constant := (129826493822750770072040839273022113229770210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536162910185463170503/100000000000000000000)
  centralHi := (67020363773182896313/12500000000000000000)
  directionLo := (538489007485326848481/100000000000000000000)
  directionHi := (269244503742663424241/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree117.table
  base := (67009836511445122880849864926433942900363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-11826369639532031550861138740963500000000000)
      constant := (350517273811805126235334349830383007090943923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree117.table
  base := (1635982170660824253211725382045375881/244140625000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1482067567775948707625808129612312500000000)
      constant := (44033322356819911708041877040351141890797120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538489007485326848481/100000000000000000000)
  centralHi := (269244503742663424241/50000000000000000000)
  directionLo := (135201274981626870493/25000000000000000000)
  directionHi := (540805099926507481973/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree118.table
  base := (34359000357083863863367598344596804808523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-161020643270084592764737054696067250000000000)
      constant := (4814132851557165992911791447282288261309444641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree118.table
  base := (34358997267362877981015434406399602046557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-5978941915340950118054998477006750000000000)
      constant := (179190884907538663013572084995151914347633397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135201274981626870493/25000000000000000000)
  centralHi := (540805099926507481973/100000000000000000000)
  directionLo := (108622263101172236829/20000000000000000000)
  directionHi := (271555657752930592073/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree119.table
  base := (17611309504562639226212442253974989878447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-81192648203243379796424368194563625000000000)
      constant := (2448494548473339102403084698980836416932886349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree119.table
  base := (70445232404110830965609000400404558582183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-36177681357468632433640586613385500000000000)
      constant := (1093648669146527808871364223345698604765332429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108622263101172236829/20000000000000000000)
  centralHi := (271555657752930592073/50000000000000000000)
  directionLo := (136351944878523468969/25000000000000000000)
  directionHi := (545407779514093875877/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree120.table
  base := (18047887054947833368769196819579058367403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-3032406473016461600388155890410875000000000)
      constant := (92232443190645027231082718346724066062455763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree120.table
  base := (72191543119599362993933321711685838202747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-12160570407630521386317060788243500000000000)
      constant := (370769938531797514419435974988931486422532387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136351944878523468969/25000000000000000000)
  centralHi := (545407779514093875877/100000000000000000000)
  directionLo := (547694614615190266591/100000000000000000000)
  directionHi := (17115456706724695831/3125000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree121.table
  base := (36978465567555302163660819490589657764861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (1512)
      previous := (756)
      next := (756)
      square := (11393208003357608026906433430000000000000)
      linear := (-1364583493217281762389025617977250000000000)
      constant := (41858027746294094241928463438475670759651247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree121.table
  base := (36978463251069258406705121139871824860177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (56)
      previous := (28)
      next := (28)
      square := (421970666791022519515053090000000000000)
      linear := (-50669064859937322154630548369250000000000)
      constant := (1558028579513539947730673748615309324860177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547694614615190266591/100000000000000000000)
  centralHi := (17115456706724695831/3125000000000000000)
  directionLo := (137492985230717574189/25000000000000000000)
  directionHi := (549971940922870296757/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree122.table
  base := (75741386598748787533361177502386736347851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-332958511631386520154367562936614500000000000)
      constant := (10299594743393323552222097487903676467648429217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree122.table
  base := (15148276478096536928550782231237622392703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-37089770953737427609572373867420500000000000)
      constant := (1150105468482308029629241109035193409642755945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137492985230717574189/25000000000000000000)
  centralHi := (549971940922870296757/100000000000000000000)
  directionLo := (552239876074207886453/100000000000000000000)
  directionHi := (276119938037103943227/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree123.table
  base := (77544914461661537360273639137058868057573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (40656)
      previous := (20328)
      next := (20328)
      square := (306350704090282349167928543340000000000000)
      linear := (-37298646433798983756732325146970500000000000)
      constant := (1163439994497021477830411798533338869104898999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree123.table
  base := (19386227659856299884902545109018483611703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25529225340856862430660711945000000000000)
      linear := (-3116150068263363277906914134897125000000000)
      constant := (97436664567426383824045772658227986517016063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552239876074207886453/100000000000000000000)
  centralHi := (276119938037103943227/50000000000000000000)
  directionLo := (554498535300539664339/100000000000000000000)
  directionHi := (27724926765026983217/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree124.table
  base := (79367514589593792235580016142947053467747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-338417124176995187466814289708854500000000000)
      constant := (10643738335404168765144225330506306023679129449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree124.table
  base := (496046944488784874695270903864112463279/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1570742945190970460841398557087937500000000)
      constant := (49522177819157903167781273707851120911135180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554498535300539664339/100000000000000000000)
  centralHi := (27724926765026983217/5000000000000000000)
  directionLo := (556748031495784617553/100000000000000000000)
  directionHi := (278374015747892308777/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree125.table
  base := (40604593430807407501088970124253615749183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (182952)
      previous := (91476)
      next := (91476)
      square := (1378578168406270571255678445030000000000000)
      linear := (-170573215224899760561518826547487250000000000)
      constant := (5408964948895584613970700740939655312652580861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree125.table
  base := (20302295927268720625124746567622101779601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (10164)
      previous := (5082)
      next := (5082)
      square := (76587676022570587291982135835000000000000)
      linear := (-9500465137501555696376040280363875000000000)
      constant := (301995586747896093399484486694089791695995163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556748031495784617553/100000000000000000000)
  centralHi := (278374015747892308777/50000000000000000000)
  directionLo := (279494237641144637929/50000000000000000000)
  directionHi := (558988475282289275859/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree126.table
  base := (5191870698049892896143349203792760388749/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12764612670428431215330355972500000000000)
      linear := (-1592017299641684512866949150375437500000000)
      constant := (50895993691103390757597220172594223014077258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree126.table
  base := (41534964153001734749462574023844404189461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-6384315069238192418469126145466750000000000)
      constant := (204598368794335323353533890791044985406924781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279494237641144637929/50000000000000000000)
  centralHi := (558988475282289275859/100000000000000000000)
  directionLo := (280609987537153547477/50000000000000000000)
  directionHi := (112243995014861418991/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree127.table
  base := (84949747413033090313802377379997204525923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (365904)
      previous := (182952)
      next := (182952)
      square := (2757156336812541142511356890060000000000000)
      linear := (-346605042995408188435484379867214500000000000)
      constant := (11170552553545129276499302554504527367186190441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree127.table
  base := (42474872406758527706876160557760554609637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (51058450681713724861321423890000000000000)
      linear := (-6434986713475347706020892104024250000000000)
      constant := (207892644158069201658025238531882402107766077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280609987537153547477/50000000000000000000)
  centralHi := (112243995014861418991/20000000000000000000)
  directionLo := (563442637139215108921/100000000000000000000)
  directionHi := (281721318569607554461/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree128.table
  base := (21712158876487963222219690565549116172799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (91476)
      previous := (45738)
      next := (45738)
      square := (689289084203135285627839222515000000000000)
      linear := (-87333587317053130522926935813333625000000000)
      constant := (2837245911575715908882050101777792962536534333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree128.table
  base := (169626236612594335181687987406636861711/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 453750000000000000000000000000000000000000
      center := (5082)
      previous := (2541)
      next := (2541)
      square := (38293838011285293645991067917500000000000)
      linear := (-4864243768284377245179493546936312500000000)
      constant := (158409912938448504803672760651477987571269952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell056.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563442637139215108921/100000000000000000000)
  centralHi := (281721318569607554461/50000000000000000000)
  directionLo := (113131313131313131313/20000000000000000000)
  directionHi := (282828282828282828283/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree129.table
  base := (88766595367965575210873987471861077461809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-13039394649667290953627078023683500000000000)
      constant := (426993626492278452647262579050361690372878889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 131
  qDenominator := 264
  table := BinomialMassData.Q131_264.Degree129.table
  base := (17753318644998495305648905326350776303453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (102116901363427449722642847780000000000000)
      linear := (-13072660003899316562248848042278500000000000)
      constant := (429120176138477503394510370388777594663589065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q131_264.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell056.Kernel129
